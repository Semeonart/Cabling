(* ::Package:: *)

BeginPackage["Cabling`"]

Needs["Representations`"]

Begin["`AdvancedSort`"]

debug=False;

Partitions[n_]:=Partitions[n]=IntegerPartitions[n];

Num[rep_]:=Num[rep]=Module[
	{partitions,pos}
,
	partitions=Partitions[Total[rep]];
	pos=Position[partitions,rep];
	If[Length[pos]!=1,Print["Partitions position failed"]];
	pos=pos[[1,1]];
	Return[pos-1];
];

PathNum[path_,n_]:=Module[
	{ans=0,tmppath,i}
,
	tmppath=Delete[path,{{-n-1},{-n},{-n+1}}];
	(*Setting two leading ordering parameters*)
	ans+=Num[path[[-n+1]]];
	ans*=Length[Partitions[n+1]];
	ans+=Num[path[[-n-1]]];
	(*Setting the remaining path, first element is a number of the path*)
	For[i=Length[tmppath],i>0,i--,
		ans*=Length[Partitions[Total[tmppath[[i]]]]];
		ans+=Num[tmppath[[i]]];
	];
	(*Setting the least leading parameter*)
	ans*=Length[Partitions[n]];
	ans+=Length[Partitions[n]]-Num[path[[-n]]];
	Return[-ans];
];

SortPaths[paths_,n_]:=Module[
	{tmppaths,i}
,
	If[debug,Print["Starting advanced sort"]];
	tmppaths=Table[{i,PathNum[paths[[i]],n]},{i,1,Length[paths]}];
	If[debug,
		Print["Sort parameter added"];
		Print[MatrixForm[tmppaths]];
	];
	tmppaths=SortBy[tmppaths,Last];
	If[debug,
		Print["Sort completed"];
		Print[MatrixForm[tmppaths]];
	];
	tmppaths=Map[(#[[1]]&),tmppaths];
	(*
	nums=Table[0,{i,1,Length[paths]}];
	For[i=1,i<=Length[paths],i++,
		nums[[tmppaths[[i]]]]=i;
	];
	If[debug,Print["Permutation finished"]];*)
	Return[tmppaths];
];

End[]

Begin["`AlgebraicR`"]
(*Cache settings*)
datadir=FileNameJoin[{NotebookDirectory[],"data","cabling"}];
(*debug settings*)
silent=True;
debug=False;
timedebug=False;
(*Transfer definitions from Representations package*)
CutYoung:=Representations`Main`CutYoung;
CheckYoung:=Representations`Main`CheckYoung;
ListPartitionsNum:=Representations`Main`ListPartitionsNum;


GetChildren[rep_]:=GetChildren[rep]=Module[
	{trep,i,ans={}}
,
	For[i=1,i<=Length[rep],i++,
		trep=rep;
		trep[[i]]--;
		If[CheckYoung[trep],
			trep=CutYoung[trep];
			AppendTo[ans,trep];
		]
	];
	ans=DeleteDuplicates[ans];
	Return[ans];
];

GetGraph[rep_]:=Module[
	{edgeslist={},levels={{rep}},children={},i,level=1,Tchildren,tpoint}
,
	For[level=1,level<Total[rep],level++,
		For[i=1,i<=Length[levels[[level]]],i++,
			Tchildren=GetChildren[tpoint=levels[[level,i]]];
			Map[AppendTo[edgeslist,DirectedEdge[tpoint,#]]&,Tchildren];
			children=Join[children,Tchildren];
		];
		children=DeleteDuplicates[children];
		AppendTo[levels,children];
		children={};
	];
	Return[edgeslist];
];

PrintGraph[rep_]:=Module[
	{edgeslist}
,
	edgeslist=GetGraph[rep];
	Print[Graph[edgeslist,VertexLabels->"Name"]];
];

GetPaths[rep_]:=GetPaths[rep]=Module[
	{children,i=0,ans={},tmp}
,
	If[rep=={1},Return[{{{1}}}]];
	children=GetChildren[rep];
	For[i=1,i<=Length[children],i++,
		tmp=GetPaths[children[[i]]];
		tmp=Map[(Prepend[#,rep])&,tmp];
		ans=Join[ans,tmp];
	];
	Return[ans];
];

AuxR1[rep_,q_]:=Switch[rep,
{2},
	Return[q],
{1,1},
	Return[-1/q],
_,
	Print["Wrong argument of AuxR1"];
	Return[Indeterminate];
];

GetR1[paths_,q_]:=Module[
	{rules={},i,ans}
,
	For[i=1,i<=Length[paths],i++,
		AppendTo[rules,{i,i}->AuxR1[paths[[i,-2]],q]];
	];
	ans=SparseArray[rules];
	Return[ans];
];

Cmp[r1_,r2_]:=Module[
	{i,rep1,rep2,l}
,
	If[AtomQ[r1]&&AtomQ[r2],
		Return[r1>r2];
	];
	l=Max[Length[r1],Length[r2]];
	rep1=PadRight[r1,l];
	rep2=PadRight[r2,l];
	For[i=1,i<=l,i++,
		If[rep1[[i]]>rep2[[i]],
			Return[False]
		];
		If[rep1[[i]]<rep2[[i]],
			Return[True]
		];
	];
	Return[Indeterminate];
];

Cmpair[rep1_,rep2_,n_]:=Module[
	{ans,i,r1,r2,trep1,trep2}
,
	(*Compare endpoints*)
	i=-n+1;
	r1=rep1[[i]];
	r2=rep2[[i]];
	If[(ans=Cmp[r1,r2])=!=Indeterminate,
		Return[ans]
	];
	i=-n-1;
	r1=rep1[[i]];
	r2=rep2[[i]];
	If[(ans=Cmp[r1,r2])=!=Indeterminate,
		Return[ans]
	];
	(*Compare remaining route*)
	trep1=Delete[rep1,{{-n+1},{-n},{-n-1}}];
	trep2=Delete[rep2,{{-n+1},{-n},{-n-1}}];
	For[i=Length[trep1],i>0,i--,
		r1=trep1[[i]];
		r2=trep2[[i]];
		If[(ans=Cmp[r1,r2])=!=Indeterminate,
			Return[ans]
		];
	];
	Return[False];
];

Num[r1_,rep2_]:=Module[
	{y,x,r2,tmp,pos}
,
	If[(Length[r1]<Length[rep2])||((Total[r1]-Total[rep2])!=2),
		Print["Wrong argument in Num[] function"];
		Return[0];
	];
	r2=PadRight[rep2,Length[r1]];
	tmp=r1-r2;
	pos=Position[tmp,1];
	y=pos[[2,1]]-pos[[1,1]];
	y=Abs[y];
	x=r1[[pos[[2,1]]]]-r1[[pos[[1,1]]]];
	x=Abs[x];
	Return[x+y];
];

SimpleBlock[i_,path1_,j_,path2_,n_,q_]:=Module[
	{r1,r2,num,cn,sn}
,
	r1=path1[[-n-1]];
	r2=path1[[-n+1]];
	num=Num[r1,r2];
	cn=1/SymbolicQ`Main`QNum[num,q];
	sn=Sqrt[1-cn^2];
	Return[{
		{i,i}->-q^-num cn,
		{i,j}->sn,
		{j,i}->sn,
		{j,j}->q^num cn
		}];
];

SingleBlock[i_,path_,n_,q_]:=Module[
	{ans,r1,r2,diff}
,
	r1=path[[-n-1]];
	r2=path[[-n+1]];
	r2=PadRight[r2,Length[r1]];
	diff=r1-r2;
	If[Position[diff,2]!={},
		ans={{i,i}->q}
	,
		ans={{i,i}->-1/q}
	];
	Return[ans];
];

GetRn[paths_,n_,a_,q_]:=Module[
	{rules={},i,ans,num,tmppaths,timestamp,ProgressBar,rule,RulesPartNum=0}
,
	If[timedebug,
		timestamp=TimeUsed[];
		Print["Starting new R-matrix"];
	];
	num=Cabling`AdvancedSort`SortPaths[paths,n];
	If[timedebug,
		Print["Sort finished, ",TimeUsed[]-timestamp];
		timestamp=TimeUsed[];
	];
	If[debug,
		Print[num];
		Print[MatrixForm[paths]];
		tmppaths=Table[Prepend[paths[[i]],i],{i,1,Length[paths]}];
		tmppaths=Sort[tmppaths,Cmpair[#1,#2,n]&];
		Print[MatrixForm[tmppaths]];
	];
	i=1;
	If[timedebug,
		timestamp=TimeUsed[];
		ProgressBar=PrintTemporary[ProgressIndicator[Dynamic[i],{0,Length[paths]}]];
	];
	While[i<=Length[paths],
		If[(i<Length[paths])&&(Delete[paths[[num[[i]]]],-n]==Delete[paths[[num[[i+1]]]],-n]),
			RulesPartNum++;
			Subscript[rule, RulesPartNum]=SimpleBlock[num[[i]],paths[[num[[i]]]],num[[i+1]],paths[[num[[i+1]]]],n,q];
			i+=2
		,
			RulesPartNum++;
			Subscript[rule, RulesPartNum]=SingleBlock[num[[i]],paths[[num[[i]]]],n,q];
			i++
		];
	];
	If[timedebug,
		Print["Rules tab finished, ",TimeUsed[]-timestamp];
		timestamp=TimeUsed[];
	];
	rules=Flatten[Table[Subscript[rule, i],{i,1,RulesPartNum}],1];
	If[timedebug,
		NotebookDelete[ProgressBar];
		Print["Block generation finished, ",TimeUsed[]-timestamp];
		timestamp=TimeUsed[];
	];
	ans=SparseArray[rules,{Length[paths],Length[paths]}];
	If[timedebug,
		Print["Sparse array generation finished"];
	];
	Return[ans];
];

GetRpaths[paths_,depth_,a_,q_]:=Module[
	{ans,i}
,
	(*Print["GetRPaths started"];*)
	ans=Table[GetRn[paths,i,a,q],{i,2,depth}];
	(*Print["Tabulation of Rn finished"];*)
	PrependTo[ans,GetR1[paths,q]];
	ans={ans,ans};
	ans[[2]]=Map[SparseArray[ArrayRules[#]/.{q->1/q},Dimensions[#]]&,ans[[2]]];
	If[debug,
		For[i=1,i<=Length[ans[[1]]],i++,
			Print["R_",i,"    ",MatrixForm[ans[[1,i]]]];
			Print["R_",i,"^-1 ",MatrixForm[ans[[2,i]]]];
		];
	];
	Return[ans];
];

GetR[rep_,a_,q_]:=Module[
	{depth,paths}
,
	If[debug,
		PrintGraph[rep];
	];
	depth=Total[rep]-1;
	paths=GetPaths[rep];
	If[!silent,
		Print["Total number of paths ",Length[paths]];
	];
	Return[GetRpaths[paths,depth,a,q]];
];

DataFileName[rep_]:=Module[
	{ans,tot}
,
	tot=Total[rep];
	tot=ToString[tot];
	ans=Map[(ToString[#]<>",")&,rep];
	ans=StringJoin[ans];
	ans=StringReplacePart[ans,"",{-1,-1}];
	ans="RTab["<>ans<>"].mx";
	ans=FileNameJoin[{datadir,tot,ans}];
	(*Print[ans];*)
	Return[ans];
];

CachedGetR[rep_,a_,q_]:=Module[
	{file,ans}
,
	file=DataFileName[rep];
	If[FileExistsQ[file],
		Return[Import[file]]
	,
		ans=GetR[rep,a,q];
		Export[file,ans,"MX"];
		Return[ans];
	];
];

CheckCachedR[rep_,a_,q_]:=Module[
	{file,rules,ans,dims}
,
	file=DataFileName[rep];
	If[FileExistsQ[file],
		ans=Import[file];
		ans=ans-GetR[rep,a,q];
		rules=ArrayRules[ans];
		rules=Map[FullSimplify[#[[2]]]&,rules];
		ans=Apply[And,Map[(#==0)&,rules]];
		If[ans,
			Print["Ok, rep=",rep]
		,
			Print["Failed, rep=",rep]
		];
	,
		Print["No cached R, rep=",rep];
		Return[False];
	];
];

CacheAllR[R_,a_,q_]:=Module[
	{rTab,counter=0,ProgressBar}
,
	rTab=IntegerPartitions[R];
	DistributeDefinitions["Cabling`AlgebraicR`",rTab];
	SetSharedVariable[counter];
	ProgressBar=PrintTemporary[ProgressIndicator[counter,{0,Length[rTab]}]];
	ParallelMap[(counter++;CachedGetR[#,a,q])&,rTab];
	NotebookDelete[ProgressBar];
];

GetP[r_,Q_]:=Module[
	{ans={},paths,rules={},i}
,
	paths=GetPaths[Q];
	For[i=1,i<=Length[paths],i++,
		If[paths[[i,-Total[r]]]==r,AppendTo[rules,{i,i}->1]];
	];
	ans=SparseArray[rules,{Length[paths],Length[paths]}];
	Return[ans];
];

End[]

Begin["`BuiltInTr`"]

(*debug settings*)
silent=False;
debug=False;
analyzesparse=False;
sparselowerbound=1000;
CutOffValue=10.^-10;

AnalyzeSparse[M_]:=Module[
	{arrayrules,dist}
,
	If[True,
		arrayrules=ArrayRules[M];
		If[Length[arrayrules]>sparselowerbound,
			Print[arrayrules];
			dist=Map[Abs[#[[2]]]&,arrayrules];
			Print[Histogram[dist,"Log"]];
		];
	];
];

CutOff[M_]:=Module[
	{dims,rules,cutrules,pos}
,
	dims=Dimensions[M];
	rules=ArrayRules[M];
	cutrules=Map[If[Abs[#[[2]]]<CutOffValue,#[[1]]->0,#]&,rules];
	(*pos=Position[cutrules,Null];
	rules=Delete[cutrules,pos];*)
	Return[SparseArray[cutrules,dims]];
];

TrF[cabledbraid_,RTab_,a_,q_,\[Chi]_]:=Module[
	{(*ProgressBar,*)i,M,ans}
,
	M=Table[KroneckerDelta[i-j],{i,1,Dimensions[RTab][[2]]},{j,1,Dimensions[RTab][[2]]}];
	(*ProgressBar=PrintTemporary[ProgressIndicator[Dynamic[i],{0,Length[cabledbraid]}]];*)
	For[i=1,i<=Length[cabledbraid],i++,
		M=M.RTab[[cabledbraid[[i]]]];
		(*If[Dimensions[M][[1]]>1000,
			M=CutOff[M];
		];*)
	];
	(*NotebookDelete[ProgressBar];*)
	If[analyzesparse,AnalyzeSparse[M]];
	ans=\[Chi] Tr[M];
	(*ans=FullSimplify[ans];*)
	Return[ans];
];

End[]

Begin["`CUDA`"]

debug=False;
TimeDebug=True;
TimeTabCUDA={};
TimeTabFloat={};

Needs["CCompilerDriver`"]
(*Directory settings*)
cudadir="c:\\Program Files\\NVIDIA GPU Computing Toolkit\\CUDA\\v5.0";
sourcedir="d:\\Semeon\\ProjectRCUDA";
workingdir="d:\\Semeon\\ProjectRCUDA\\tmp";
includesrc=FileNameJoin[{cudadir,"include"}];
libsrc=FileNameJoin[{sourcedir,"RCUDA.c"}];
libdir=FileNameJoin[{cudadir,"lib\\x64"}];
cudartlib=FileNameJoin[{libdir,"cudart.lib"}];
cusparselib=FileNameJoin[{libdir,"cusparse.lib"}];
iniCUDA=FileNameJoin[{NotebookDirectory[],"RCUDA.ini"}]
(*Cleaning the old defintions of functions to overwrite .dll*)
LibraryFunctionUnload[SparseTr];
(*Library compilation*)
If[FileExistsQ[iniCUDA],
	Rlib=Import[iniCUDA];
,
	Rlib=CreateLibrary[{libsrc},"RCUDA","WorkingDirectory"->workingdir,
		"CleanIntermediate"->True,"IncludeDirectories"->{includesrc},
		"Libraries"->{cudartlib,cusparselib},"Debug"->False,"CompileOptions"->"/Zi"];
	Export[iniCUDA,Rlib];
];
(*Loading functions from compiled library*)
SparseTr=LibraryFunctionLoad[Rlib,"SparseTr",{Integer,{Integer,1},{Integer,2},
	{Integer,2},{Complex,2},{Integer,1},Integer},Complex];

CmpRules[rule1_,rule2_]:=(
	If[rule1[[1]]<rule2[[1]],
		Return[True];
	];
	If[rule1[[1]]>rule2[[1]],
		Return[False];
	];
	If[rule1[[2]]<rule2[[2]],
		Return[True]
	,
		Return[False]
	];
);
(*Conversion of a sparse matrix to pass it into compiled library*)
ConvertMatrix[R_]:=Module[
	{rules}
,
	rules=ArrayRules[R];
	rules=Map[{#[[1,1]],#[[1,2]],#[[2]]}&,rules];
	rules=Delete[rules,-1];
	rules=Sort[rules,CmpRules];
	Return[rules];
];
ConvertMatrixSet[RTab_]:=Module[
	{tmp,nnz}
,
	If[debug,Print["Entering Matrix Conversion"]];
	(*DistributeDefinitions[CmpRules,ConvertMatrix,RTab];
	Print["Definitions expanded to all kernels"];*)
	tmp=Map[ConvertMatrix,RTab];
	If[debug,Print["Conversion of table finished"]];
	nnz=Map[Length,tmp];
	tmp=PadRight[tmp];
	tmp=Transpose[tmp,{2,3,1}];
	PrependTo[tmp,nnz];
	Return[tmp];
];

(*CUDA Tr multiplication*)
TrF[cabledbraid_,RTab0_,a_,q_,\[Chi]_]:=Module[
	{ans,cudaRbraid,nnz,RowR,ColR,ValR,RTab}
,
	(*Converting braid*)
	cudaRbraid=Map[If[(#>0),#-1,#+Length[RTab0]]&,cabledbraid];
	(*Converting RTab to form used by CUDA Auxiliary*)
	RTab=ConvertMatrixSet[RTab0];
	nnz=RTab[[1]];
	RowR=RTab[[2]];
	ColR=RTab[[3]];
	ValR=RTab[[4]];
	ans=SparseTr[Length[nnz],nnz,RowR,ColR,ValR,cudaRbraid,Dimensions[RTab0][[2]]];
	(*Print[MatrixForm[ans]];*)
	Return[\[Chi] ans];
];

MixedTrF[cabledbraid_,RTab_,a_,q_,\[Chi]_]:=Module[
	{TimeStart,n,ans}
,
	n=Length[RTab[[1]]];
	If[TimeDebug,
		TimeStart=TimeUsed[];
	];
	If[n>600,
		ans=TrF[cabledbraid,RTab,a,q,\[Chi]];
		If[TimeDebug,
			AppendTo[TimeTabCUDA,{n,TimeUsed[]-TimeStart}];
		]
	,
		ans=Cabling`BuiltInTr`TrF[cabledbraid,RTab,a,q,\[Chi]];
		If[TimeDebug,
			AppendTo[TimeTabFloat,{n,TimeUsed[]-TimeStart}];
		];
	];
	Return[ans];
];

End[]

Begin["`FloatH`"]

\[CapitalLambda]a:=Cabling`Fourier`\[CapitalLambda]a;
\[CapitalLambda]q:=Cabling`Fourier`\[CapitalLambda]q;
DefaultPrecision=4 $MachinePrecision;

TableTr[cabledbraid_,RTab0_,a_,q_,\[Chi]0_,powa_,powq_,NormF_,TrF_]:=Module[
	{numa,numq,ans,ProgressBar1,ProgressBar2,i,a0,j,q0,RTab,tmp,\[Chi]}
,
	numa=powa[[2]]-powa[[1]]+1;
	numq=powq[[2]]-powq[[1]]+1;
	ans=Table[0,{i,1,numa},{j,1,numq}];
	ProgressBar1=PrintTemporary[ProgressIndicator[Dynamic[i],{0,numa}]];
	ProgressBar2=PrintTemporary[ProgressIndicator[Dynamic[j],{0,numq}]];
	For[i=0,i<numa,i++,
		a0=\[CapitalLambda]a Exp[\[Pi] I i/numa];
		a0=N[a0,DefaultPrecision];
		For[j=0,j<numq,j++,
			q0=\[CapitalLambda]q Exp[\[Pi] I j/numq];
			q0=N[q0,DefaultPrecision];
			RTab=Map[SparseArray[ArrayRules[#]/.{a->a0,q->q0},Dimensions[#]]&,RTab0];
			tmp=NormF;
			tmp=tmp/.{a->a0,q->q0};
			\[Chi]=\[Chi]0/.{a->a0,q->q0};
			tmp=tmp TrF[cabledbraid,RTab,a,q,\[Chi]];
			ans[[i+1,j+1]]=tmp;
		];
	];
	NotebookDelete[ProgressBar2];
	NotebookDelete[ProgressBar1];
	Return[ans];
];

End[]

Begin["`MultiSummationQ`"]

debug=False;
silent=True;
Ga=Global`a;
Gq=Global`q;

GetRPTab[Q_,repTab_,a_,q_]:=Module[
	{RTab,PTab}
,
	RTab=Cabling`AlgebraicR`CachedGetR[Q,Ga,Gq];
	RTab=Map[SparseArray[ArrayRules[#]/.{Ga->a,Gq->q},Dimensions[#]]&,RTab,2];
	PTab=Map[Cabling`AlgebraicR`GetP[#,Q]&,repTab];
	RTab=Join[RTab[[1]],PTab,Reverse[RTab[[2]]]];
	Return[RTab];
];

Include[rep_,Q_]:=Module[
	{i}
,
	If[Length[rep]>Length[Q],
		Return[False];
	];
	For[i=1,i<=Length[rep],i++,
		If[rep[[i]]>Q[[i]],
			Return[False];
		];
	];
	Return[True];
];

(*This function provides a summation over all Q*)
H[cabledbraid_,strandnum_,repTab_,a_,q_,TrF_]:=Module[
	{Q={},Q0,ProgressBar,i,tmp,ans,includedpaths,RTab}
,
	(*Generating set of potential Q*)
	Q0=IntegerPartitions[strandnum];
	(*Sorting out Q which have nonzero projection*)
	For[i=1,i<=Length[Q0],i++,
		includedpaths=Map[Include[#,Q0[[i]]]&,repTab];
		If[Apply[And,includedpaths],
			AppendTo[Q,Q0[[i]]];
		];
	];
	If[!silent,
		Print["Total number of Q ",Length[Q]];
	];
	(*Starting main cycle of summatoin over Q*)
	ProgressBar=PrintTemporary[ProgressIndicator[Dynamic[i],{0,Length[Q]}]];
	For[i=1,i<=Length[Q],i++,
		If[debug,
			Print["Starting with Q=",Q[[i]]];
		];
		RTab=GetRPTab[Q[[i]],repTab,a,q];
		tmp=TrF[cabledbraid,RTab,a,q,Representations`Main`\[Chi]Special[Q[[i]],a,q]];
		tmp=tmp;
		If[i==1,
			ans=tmp
		,
			ans=ans+tmp;
		];
	];
	NotebookDelete[ProgressBar];
	ProgressBar=PrintTemporary["Simplification of HOMFLY polynomial"];
	ans=FullSimplify[ans];
	ans=Factor[ans];
	NotebookDelete[ProgressBar];
	Return[ans];
];

End[]

Begin["`Fourier`"]

debug=False;
silent=False;

(*settings for Fourier*)
powaSet=Null;
powqSet=Null;
\[CapitalLambda]a=(*0.540942;*)Random[Real,{0.8,0.9}];
\[CapitalLambda]q=(*1.81391;*)Random[Real,{1.1,1.2}];
\[Epsilon]=0.000001;
Print["\[CapitalLambda]a=",\[CapitalLambda]a,", \[CapitalLambda]q=",\[CapitalLambda]q,", \[Epsilon]=",\[Epsilon]];

GetPows[ftab0_,maxdepth_]:=Module[
	{ftab=ftab0,pow,i}
,
	pow={0,0};
	ftab=Flatten[ftab];
	(*Generating fourier table*)
	ftab=InverseFourier[ftab];
	ftab=Map[Abs[#]&,ftab];
	If[!silent,
		Print[ftab];
		Print[ListPlot[ftab,PlotRange->All]];
	];
	(*determining maximum power*)
	For[i=1,i<=maxdepth,i++,
		If[ftab[[i+1]]>\[Epsilon],
			pow[[2]]=i;
		];
	];
	If[pow[[2]]==maxdepth,
		Print["Warning, the maximum power is not granted"];
	];
	(*determining miminal negative power*)
	For[i=-1,i>=-maxdepth,i--,
		If[ftab[[i]]>\[Epsilon],
			pow[[1]]=i;
		];
	];
	If[pow[[1]]==-maxdepth,
		Print["Warning, the minimum power is not granted"];
	];
	Return[pow];
];

RestorePolynomial[ftab_,a_,q_,powa_,powq_]:=Module[
	{ans=0,ctab,numa,numq,i,j,i0,j0,c}
,
	numa=powa[[2]]-powa[[1]]+1;
	numq=powq[[2]]-powq[[1]]+1;
	ctab=InverseFourier[ftab];
	ctab=Map[(#/Sqrt[numa numq])&,ctab];
	Print[MatrixForm[ctab]];
	For[i=powa[[1]],i<=powa[[2]],i++,
		If[i<0,i0=i,i0=i+1];
		For[j=powq[[1]],j<=powq[[2]],j++,
			If[j<0,j0=j,j0=j+1];
			c=ctab[[i0,j0]];
			c=c \[CapitalLambda]a^(-2i) \[CapitalLambda]q^(-2j);
			If[Abs[c-Round[c]]>\[Epsilon],
				Print["Failed to restore a polynomial, c=",c,", \[CapitalLambda]a=",\[CapitalLambda]a,", \[CapitalLambda]q=",\[CapitalLambda]q,", i=",i,", j=",j];
				Return[Indeterminate];
			];
			If[Round[c]!=0,
				ans=ans+Round[c] a^(2i) q^(2j);
			];
		];
	];
	Return[ans];
];

FourierH[cabledbraid_,strandnum_,repTab_,a_,q_,TrF_,NormF0_,maxdepth_]:=Module[
	{powa0,powq0,ftab,powa,powq,HOMFLY,NormF=NormF0}
,
	(*Determining powa*)
	If[powaSet==Null,
		powa0={-maxdepth,maxdepth};
		powq0={0,0};
		ftab=Cabling`MultiSummationQ`H[cabledbraid,strandnum,repTab,a,q,Cabling`FloatH`TableTr[##,powa0,powq0,NormF,TrF]&];
		powa=GetPows[ftab,maxdepth];
		If[powa==powa0,
			powq0={0,0};
			NormF=NormF a;
			ftab=Cabling`MultiSummationQ`H[cabledbraid,strandnum,repTab,a,q,Cabling`FloatH`TableTr[##,powa0,powq0,NormF,TrF]&];
			powa=GetPows[ftab,maxdepth];
		]
	,
		powa=powaSet;
	];
	Print["powa=",powa];
	(*Determining powq*)
	If[powqSet==Null,
		powa0={0,0};
		powq0={-maxdepth,maxdepth};
		ftab=Cabling`MultiSummationQ`H[cabledbraid,strandnum,repTab,a,q,Cabling`FloatH`TableTr[##,powa0,powq0,NormF,TrF]&];
		powq=GetPows[ftab,maxdepth];
		If[powq==powq0,
			NormF=NormF q;
			powa0={0,0};
			ftab=Cabling`MultiSummationQ`H[cabledbraid,strandnum,repTab,a,q,Cabling`FloatH`TableTr[##,powa0,powq0,NormF,TrF]&];
			powq=GetPows[ftab,maxdepth];
		]
	,
		powq=powqSet;
	];
	Print["powq=",powq];
	(*Generating main table*)
	ftab=Cabling`MultiSummationQ`H[cabledbraid,strandnum,repTab,a,q,Cabling`FloatH`TableTr[##,powa,powq,NormF,TrF]&];
	Print[MatrixForm[ftab]];
	HOMFLY=RestorePolynomial[ftab,a,q,powa,powq];
	HOMFLY=HOMFLY/NormF;
	Return[HOMFLY];
];

End[]

Begin["`Multicomponent`"]

debug=False;

(*Construction of cabled braid*)
GetCabledBraid[braidword_,repTabAll_,repStrand0_]:=Module[
	{cabledbraid={},accumulateTab,i,j,k,n,sign,nCabled,repStrand,repTab}
,
	repStrand=repStrand0;
	For[i=1,i<=Length[braidword],i++,
		(*Generating the table of representations*)
		repTab=Table[repTabAll[[repStrand[[i]]]],{i,1,Length[repStrand]}];
		(*Generating the table of shifts*)
		accumulateTab=Accumulate[Map[Total,repTab]];
		PrependTo[accumulateTab,0];
		n=braidword[[i]];
		sign=Sign[n];
		n=Abs[n];
		(*Adding projector*)
		AppendTo[cabledbraid,accumulateTab[[-1]]+repStrand[[1]]-1];
		(*Generating cabled intersection*)
		For[j=Total[repTab[[n]]],j>=1,j--,
			For[k=0,k<Total[repTab[[n+1]]],k++,
				nCabled=accumulateTab[[n]]+j+k;
				nCabled*=sign;
				AppendTo[cabledbraid,nCabled];
			];
		];
		(*Permuting the representation table*)
		repStrand=Permute[repStrand,Cycles[{{n,n+1}}]];
	];
	If[debug,
		Print["Cabled braid ",cabledbraid];
	];
	If[repStrand!=repStrand0,
		Print["Failed to return strands in original representation"];
	];
	Return[cabledbraid];
];

(*Integrated functions to call outside*)
HOMFLY[braidword_,repTab_,repStrand_,a_,q_,HF_]:=Module[
	{cabledbraid,strandnum}
,
	strandnum=Sum[Total[repTab[[repStrand[[i]]]]],{i,1,Length[repStrand]}];
	cabledbraid=GetCabledBraid[braidword,repTab,repStrand];
	Return[HF[cabledbraid,strandnum,repTab,a,q]];
];

AlgebraicHOMFLY[braidword_,repTab_,repStrand_,a_,q_]:=
	HOMFLY[braidword,repTab,repStrand,a,q,
	Cabling`MultiSummationQ`H[##,Cabling`BuiltInTr`TrF]&];

FourierHOMFLY[braidword_,repTab_,repStrand_,a_,q_,NormF_,maxdepth_]:=
	HOMFLY[braidword,repTab,repStrand,a,q,
	Cabling`Fourier`FourierH[##,Cabling`BuiltInTr`TrF,NormF,maxdepth]&];

CUDAFourierHOMFLY[braidword_,repTab_,repStrand_,a_,q_,NormF_,maxdepth_]:=
	HOMFLY[braidword,repTab,repStrand,a,q,
	Cabling`Fourier`FourierH[##,Cabling`CUDA`MixedTrF,NormF,maxdepth]&];

End[]

EndPackage[]



