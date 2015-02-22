#include "llvm/Analysis/Passes.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/MCJIT.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Transforms/Scalar.h"
#include <cctype>
#include <cstdio>
#include <string>
#include <cstdlib>
#include <map>
#include <vector>
using namespace llvm;

//--------------constant-----------------

enum Token
{
	tok_eof = -1,
	tok_def = -2,
	tok_extern = -3,
	tok_identifier = -4,
	tok_number = -5,
};

static std::string IdentifierStr;
static double NumVal;

//---------------lexer---------------------

static int gettok() {
	static int LastChar = ' ';

	while (isspace(LastChar))
		LastChar = getchar();

	if (isalpha(LastChar)) {
		IdentifierStr = LastChar;
		while (isalnum(LastChar = getchar()))
			IdentifierStr += LastChar;

		if (IdentifierStr == "def") return tok_def;
		if (IdentifierStr == "extern") return tok_extern;
		return tok_identifier;
	}

	if (isdigit(LastChar) || LastChar == '.') {
		std::string NumStr;
		do {
			NumStr += LastChar;
			LastChar = getchar();
		} while (isdigit(LastChar) || LastChar == '.');

		NumVal = strtod(NumStr.c_str(), 0);
		return tok_number;
	}

	if (LastChar == '#') {
		do LastChar = getchar();
		while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');

		if (LastChar != EOF)
			return gettok();
	}

	if (LastChar == EOF)
		return tok_eof;

	int ThisChar = LastChar;
	LastChar = getchar();
	return ThisChar;
}

//-------------------abstract syntax tree-------------------------

class ExprAST {
public:
	virtual ~ExprAST() {}
	virtual Value *Codegen() = 0;
};

class NumberExprAST : public ExprAST {
	double Val;
public:
	NumberExprAST(double val): Val(val) {}
	virtual Value *Codegen();
};

class VariableExprAST : public ExprAST {
	std::string Name;
public:
	VariableExprAST(const std::string &name): Name(name) {}
	virtual Value *Codegen();
};

class BinaryExprAST : public ExprAST {
	char Op;
	ExprAST *LHS, *RHS;
public:
	BinaryExprAST(char op, ExprAST *lhs, ExprAST *rhs) : Op(op), LHS(lhs), RHS(rhs) {}
	virtual Value *Codegen();
};

class CallExprAST : public ExprAST {
	std::string Callee;
	std::vector<ExprAST*> Args;
public:
	CallExprAST(const std::string &callee, std::vector<ExprAST*> &args): Callee(callee), Args(args) {}
	virtual Value *Codegen();
};

/**
*@class the prototype of the function we define
**/
class PrototypeAST {
	std::string Name;
	std::vector<std::string> Args;
public:
	PrototypeAST(const std::string &name, const std::vector<std::string> &args) : Name(name), Args(args) {}
	virtual Function *Codegen();
};

class FunctionAST {
	PrototypeAST *Proto;
	ExprAST *Body;
public:
	FunctionAST(PrototypeAST *proto, ExprAST *body) : Proto(proto), Body(body) {}
	virtual Function *Codegen();
};


static int CurTok;
static int getNextToken() {
	return CurTok = gettok();
}

ExprAST *Error(const char *Str) {
	fprintf(stderr, "Error: %s\n", Str);
	return 0;
}

PrototypeAST *ErrorP(const char *Str) {
	Error(Str);
	return 0;
}

FunctionAST *ErrorF(const char *Str) {
	Error(Str);
	return 0;
}

//NumberExpr ::= number
static ExprAST *ParseNumberExpr() {
	ExprAST *Result = new NumberExprAST(NumVal);
	getNextToken();
	return Result;
}

//declare
static ExprAST *ParseExpression();

//ParanExpr ::= '(' expression ')'
static ExprAST *ParseParanExpr() {
	getNextToken(); // eat '('
	ExprAST *V = ParseExpression();
	if (!V) return 0;
	if (CurTok != ')')
		return Error("expected ')'");
	getNextToken(); // eat ')'
	return V;
}

//Identifier ::= identifier 
//Identifier ::= identifier '(' expression* ')'
static ExprAST *ParseIdentifierExpr() {
	std::string IdName = IdentifierStr;
	getNextToken();

	if (CurTok != '(')
		return new VariableExprAST(IdName);

	getNextToken();
	std::vector<ExprAST*> Args;
	if (CurTok != ')') {
		while (1) {
			ExprAST *Arg = ParseExpression();
			if (!Arg) return 0;
			Args.push_back(Arg);

			if (CurTok == ')') break;

			if (CurTok != ',')
				return Error("expected ')' or ',' in argument list");
			getNextToken();
		}
	}
	getNextToken();

	return new CallExprAST(IdName, Args);
}

//primary ::= identifier | number | parenexpre
static ExprAST *ParsePrimary() {
	switch (CurTok) {
		case tok_identifier: return ParseIdentifierExpr();
		case tok_number: return ParseNumberExpr();
		case '(': return ParseParanExpr();
		default: return Error("unknown token when expecting an expression");
	}
}

static std::map<char, int> BinopPrecedence;

static int GetTokPrecedence() {
	if (!isascii(CurTok))
		return -1;

	int TokPrec = BinopPrecedence[CurTok];
	if (TokPrec <= 0)
		return -1;

	return TokPrec;
}

//binoprhs ::= ( '+' primary)*
static ExprAST *ParseBinOpRHS(int ExprPrec, ExprAST *LHS) {
	while (1) {
		int TokPrec = GetTokPrecedence();
		if (TokPrec < ExprPrec)
			return LHS;
		int BinOp = CurTok;
		getNextToken();
		ExprAST *RHS = ParsePrimary();
		if (!RHS) return 0;

		int NextPrec = GetTokPrecedence();
		if (TokPrec < NextPrec) {
			RHS = ParseBinOpRHS(TokPrec + 1, RHS);
			if (!RHS) return 0;
		}

		LHS = new BinaryExprAST(BinOp, LHS, RHS);
	}
}

// expression ::= primary binoprhs
static ExprAST *ParseExpression() {
	ExprAST *LHS = ParsePrimary();
	if (!LHS) return 0;
	return ParseBinOpRHS(0, LHS);
}

//prototype ::= id '(' id* ')'
static PrototypeAST *ParsePrototype() {
	if (CurTok != tok_identifier)
		return ErrorP("excepted function name in prototype");
	std::string FnName = IdentifierStr;
	getNextToken();

	if (CurTok != '(')
		return ErrorP("excepted '(' in prototype");

	std::vector<std::string> ArgNames;
	while (getNextToken() == tok_identifier)
		ArgNames.push_back(IdentifierStr);
	if (CurTok != ')')
		return ErrorP("expected ')' in prototype");

	getNextToken();
	return new PrototypeAST(FnName, ArgNames);
}

//definition ::= 'def' prototype expression
static FunctionAST *PraseDefinition() {
	getNextToken(); //eat def
	PrototypeAST *Proto = ParsePrototype();
	if (!Proto) return 0;

	if (ExprAST *E = ParseExpression())
		return new FunctionAST(Proto, E);
	return 0;
}

//external ::= 'extern' prototype
static PrototypeAST *ParseExtern() {
	getNextToken();//eat extern
	return ParsePrototype();
}

//topleverexpr ::= expression
static FunctionAST *ParseTopLevelExpr() {
	if (ExprAST *E = ParseExpression()) {
		//make an anonymous proto
		PrototypeAST *Proto = new PrototypeAST("", std::vector<std::string>());
		return new FunctionAST(Proto, E);
	}
	return 0;
}

//----------------quick and dirty hack---------------
std::string GenerateUniqueName(const char *root) {
	static int i = 1;
	char s[16];
	sprintf(s, "%s%d", root, i++);
	std::string S;
	return S;
}

std::string MakeLegalFunctionName(std::string Name) {
	std::string NewName;
	if (Name.length() == 0) 
		return GenerateUniqueName("anonymous_function");

	NewName =  Name;
	// the first char of a name can't be a digit
	if (NewName.find_first_of("0123456789") == 0) {
		NewName.insert(0, "funciton_");
	}

	std::string LegalElements = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
	size_t pos;
	while ((pos = NewName.find_first_not_of(LegalElements)) != std::string::npos) {
		char OldChar = NewName.at(pos);
		char NewStr[16];
		sprintf(NewStr, "%d", (int)OldChar);
		NewName =  NewName.replace(pos, 1, NewStr);
	}

	return NewName;
}

//----------------MCJIT helper class--------------
class MCJITHelper {
public:
	MCJITHelper(LLVMContext &C) : Context(C), OpenModule(NULL) {}
	~MCJITHelper();

	Function *getFunction(const std::string FnName);
	Module *getModuleForNewFunction();
	void *getPointerToFunction(Function *F);
	void *getSymbolAddress(const std::string &Name);
	void dump();

private:
	typedef std::vector<Module *> ModuleVector;
	typedef std::vector<ExecutionEngine *> EngineVector;

	LLVMContext &Context;
	Module *OpenModule;
	ModuleVector Modules;
	EngineVector Engines;
};

class HelpingMemoryManager : public SectionMemoryManager {
	HelpingMemoryManager(const HelpingMemoryManager &) = delete;
	void operator=(const HelpingMemoryManager &) = delete;

public:
	HelpingMemoryManager(MCJITHelper *Helper) : MasterHelper(Helper) {}
	virtual ~HelpingMemoryManager() {}

	/// This method returns the address of the specified symbol.
	/// Our implementation will attempt to find symbols in other
	/// modules associated with the MCJITHelper to cross link symbols
	/// from one generated module to another.
	virtual uint64_t getSymbolAddress(const std::string &Name) override;

private:
	MCJITHelper *MasterHelper;
};

uint64_t HelpingMemoryManager::getSymbolAddress(const std::string &Name) {
	uint64_t FnAddr = SectionMemoryManager::getSymbolAddress(Name);
	if (FnAddr)
		return FnAddr;

	uint64_t HelperFun = (uint64_t)MasterHelper->getSymbolAddress(Name);
	if (!HelperFun)
		report_fatal_error("Program used extern function '" + Name +
			"' which could not be resolved!");

	return HelperFun;
}

MCJITHelper::~MCJITHelper() {
	if (OpenModule)
		delete OpenModule;
	EngineVector::iterator begin = Engines.begin();
	EngineVector::iterator end = Engines.end();
	EngineVector::iterator it;
	for (it = begin; it != end; ++it)
		delete *it;
}

Function *MCJITHelper::getFunction(const std::string FnName) {
	ModuleVector::iterator begin = Modules.begin();
	ModuleVector::iterator end = Modules.end();
	ModuleVector::iterator it;
	for (it = begin; it != end; ++it) {
		Function *F = (*it)->getFunction(FnName);
		if (F) {
			if (*it == OpenModule)
				return F;

			assert(OpenModule != NULL);

			// This function is in a module that has already been JITed.
			// We need to generate a new prototype for external linkage.
			Function *PF = OpenModule->getFunction(FnName);
			if (PF && !PF->empty()) {
				ErrorF("redefinition of function across modules");
				return 0;
			}

      			// If we don't have a prototype yet, create one.
			if (!PF)
				PF = Function::Create(F->getFunctionType(), Function::ExternalLinkage,
					FnName, OpenModule);
			return PF;
		}
	}
	return NULL;
}

Module *MCJITHelper::getModuleForNewFunction() {
  	// If we have a Module that hasn't been JITed, use that.
	if (OpenModule)
		return OpenModule;

  	// Otherwise create a new Module.
	std::string ModName = GenerateUniqueName("mcjit_module_");
	Module *M = new Module(ModName, Context);
	Modules.push_back(M);
	OpenModule = M;
	return M;
}

void *MCJITHelper::getPointerToFunction(Function *F) {
  	// See if an existing instance of MCJIT has this function.
	EngineVector::iterator begin = Engines.begin();
	EngineVector::iterator end = Engines.end();
	EngineVector::iterator it;
	for (it = begin; it != end; ++it) {
		void *P = (*it)->getPointerToFunction(F);
		if (P)
			return P;
	}

  	// If we didn't find the function, see if we can generate it.
	if (OpenModule) {
		std::string ErrStr;
		ExecutionEngine *NewEngine =
		        EngineBuilder(std::unique_ptr<Module>(OpenModule))
		            .setErrorStr(&ErrStr)
		            .setMCJITMemoryManager(std::unique_ptr<HelpingMemoryManager>(
		                new HelpingMemoryManager(this)))
		            .create();
		if (!NewEngine) {
			fprintf(stderr, "Could not create ExecutionEngine: %s\n", ErrStr.c_str());
			exit(1);
		}

    		// Create a function pass manager for this engine
		auto *FPM = new legacy::FunctionPassManager(OpenModule);

    		// Set up the optimizer pipeline.  Start with registering info about how the
    		// target lays out data structures.
		OpenModule->setDataLayout(NewEngine->getDataLayout());
		FPM->add(new DataLayoutPass());
    		// Provide basic AliasAnalysis support for GVN.
		FPM->add(createBasicAliasAnalysisPass());
    		// Promote allocas to registers.
		FPM->add(createPromoteMemoryToRegisterPass());
 		// Do simple "peephole" optimizations and bit-twiddling optzns.
		FPM->add(createInstructionCombiningPass());
		// Reassociate expressions.
		FPM->add(createReassociatePass());
 		// Eliminate Common SubExpressions.
		FPM->add(createGVNPass());
		// Simplify the control flow graph (deleting unreachable blocks, etc).
		FPM->add(createCFGSimplificationPass());
		FPM->doInitialization();

 		// For each function in the module
		Module::iterator it;
		Module::iterator end = OpenModule->end();
		for (it = OpenModule->begin(); it != end; ++it) {
  		    	// Run the FPM on this function
			FPM->run(*it);
		}

    		// We don't need this anymore
		delete FPM;

		OpenModule = NULL;
		Engines.push_back(NewEngine);
		NewEngine->finalizeObject();
		return NewEngine->getPointerToFunction(F);
	}
	return NULL;
}

void *MCJITHelper::getSymbolAddress(const std::string &Name) {
	// Look for the symbol in each of our execution engines.
	EngineVector::iterator begin = Engines.begin();
	EngineVector::iterator end = Engines.end();
	EngineVector::iterator it;
	for (it = begin; it != end; ++it) {
		uint64_t FAddr = (*it)->getFunctionAddress(Name);
		if (FAddr) {
			return (void *)FAddr;
		}
	}
	return NULL;
}

void MCJITHelper::dump() {
	ModuleVector::iterator begin = Modules.begin();
	ModuleVector::iterator end = Modules.end();
	ModuleVector::iterator it;
	for (it = begin; it != end; ++it)
		(*it)->dump();
}

//---------------code generation------------------
Value *ErrorV(const char *Str) 
{
	Error(Str);
	return 0;
}

static MCJITHelper *JITHelper;
static IRBuilder<> Builder(getGlobalContext());
static std::map<std::string, Value*> NamedValues;

Value *NumberExprAST::Codegen() {
	return ConstantFP::get(getGlobalContext(), APFloat(Val));
}

Value *VariableExprAST::Codegen() {
	Value *V = NamedValues[Name];
	return V ? V : ErrorV("unknown variable name");
}

Value *BinaryExprAST::Codegen() {
	Value *L = LHS->Codegen();
	Value *R = RHS->Codegen();
	if (L ==0 || R == 0) return 0;

	switch (Op) {
		case '+' : return Builder.CreateFAdd(L, R, "addtmp");
		case '-' : return Builder.CreateFSub(L, R, "subtmp");
		case '*' : return Builder.CreateFMul(L, R, "multmp");
		case '<' :
			L  = Builder.CreateFCmpULT(L, R, "cmptmp");
			return Builder.CreateUIToFP(L, Type::getDoubleTy(getGlobalContext()), "booltmp");
		default : return ErrorV("invalid binary operator");
	}
}

Value *CallExprAST::Codegen() {
	Function *CalleeF = JITHelper->getFunction(Callee);
	if (CalleeF == 0) 
		return ErrorV("unknown function reference");
	if (CalleeF->arg_size() != Args.size())
		return ErrorV("Incorrect # arguments passed");

	std::vector<Value*> ArgsV;
	for (unsigned i = 0, e = Args.size(); i != e; ++i) {
		ArgsV.push_back(Args[i]->Codegen());
		if (ArgsV.back() == 0) return 0;
	}
	return Builder.CreateCall(CalleeF, ArgsV, "calltmp");
}

Function *PrototypeAST::Codegen() {
	std::vector<Type*> Doubles(Args.size(), Type::getDoubleTy(getGlobalContext()));
	FunctionType *FT = FunctionType::get(Type::getDoubleTy(getGlobalContext()), Doubles, false);
	std::string FnName = MakeLegalFunctionName(Name);
	Module *M = JITHelper->getModuleForNewFunction();
	Function *F = Function::Create(FT, Function::ExternalLinkage, FnName, M);
	if (F->getName() != FnName) {
		F->eraseFromParent();
		F = JITHelper->getFunction(Name);
		if (!F->empty()) {
			ErrorF("redefinition of function");
			return 0;
		}
		if (F->arg_size() != Args.size()) {
			ErrorF("redefinition of function with different # args");
			return 0;
		}
	}	

	unsigned Idx = 0;
	for (Function::arg_iterator AI = F->arg_begin(); Idx != Args.size(); ++AI, ++Idx) {
		AI->setName(Args[Idx]);
		NamedValues[Args[Idx]] = AI;
	}
	return F;
}

Function *FunctionAST::Codegen() {
	NamedValues.clear();
	Function *TheFunction = Proto->Codegen();
	if (TheFunction == 0) return 0;

	BasicBlock *BB = BasicBlock::Create(getGlobalContext(), "entry", TheFunction);
	Builder.SetInsertPoint(BB);

	if (Value *RetVal = Body->Codegen()) {
		Builder.CreateRet(RetVal);
		verifyFunction(*TheFunction);
		return TheFunction;
	}
	TheFunction->eraseFromParent();
	return 0;
}

//--------------Top-Level parsing-----------------

static void HandleDefinition() {
	if (FunctionAST *F = PraseDefinition()) {
		if (Function *LF = F->Codegen()) {
			fprintf(stderr, "Read function definition:" );
			LF->dump();
		}
	} else {
		// skip token for error recovery
		getNextToken();
	}
}

static void HandleExtern() {
	if (PrototypeAST *P = ParseExtern()) {
		if (Function *F = P->Codegen()) {
			fprintf(stderr, "Read extern: ");
			F->dump();
		}
	} else {
		// skip token for error recovery
		getNextToken();
	}
}

static void HandleTopLevelExpression() {
	if (FunctionAST *F =  ParseTopLevelExpr()) {
		if (Function *LF = F->Codegen()) {
			void *FPtr = JITHelper->getPointerToFunction(LF);
			double (*FP)() = (double (*)())(intptr_t)FPtr;
			fprintf(stderr, "Evaluated to %f\n", FP());
		}
	} else {
		getNextToken();
	}
}

// top ::= definition | external | expression | ';'
static void MainLoop() {
	while (1) {
		fprintf(stderr, "ready> " );
		switch (CurTok) {
			case tok_eof: return;
			case ';': getNextToken(); break; //ignore top-level semicolons
			case tok_def: HandleDefinition(); break;
			case tok_extern: HandleExtern(); break;
			default: HandleTopLevelExpression(); break;
		}
	}
}

extern "C"
double putchard(double x) {
	putchar((char)x);
	return 0;
}

int main(int argc, char const *argv[])
{
	InitializeNativeTarget();
	InitializeNativeTargetAsmPrinter();
	InitializeNativeTargetAsmParser();
	LLVMContext &Context = getGlobalContext();
	JITHelper = new MCJITHelper(Context);

	BinopPrecedence['<'] = 10;
	BinopPrecedence['+'] = 20;
	BinopPrecedence['-'] = 20;
	BinopPrecedence['*'] = 40;

	fprintf(stderr, "ready> " );
	getNextToken();

	
	MainLoop();

	JITHelper->dump();

	return 0;
}
