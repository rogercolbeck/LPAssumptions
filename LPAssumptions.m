(* ::Package:: *)

(* 
   Copyright 2019 LPAssumptions (https://github.com/rogercolbeck/LPAssumptions)

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

*)


(*To do list for future versions:
	1. The current version can only handle variables occuring in the objective function and nowhere else, this can be generalised for future versions.
	2. In this version, there may be many redundancies in the output of LPAssumptions and the reduction/simplification of the output needs to be done manually using Mathematica's Reduce function for example. This compression can be automated in future versions.
*)


BeginPackage["LPAssumptions`"]
(*StartTab::usage="StartTab[c,M,b] generates the initial tableau for the linear programming problem of minimizing c.x subject to M.x=b, x>=0, where each element of b is nonnegative."

SlackenMix::usage="SlackenMix[c,M,b] converts the problem of minimizing c.x subject to M.x>=b, x>=0 into the form required by StartTab by adding slack variables. It outputs {c',M',b} corresponding to minimizing c'.x subject to M.x=b, x>=0. If b is given as a list of pairs, the second entry in the list gives whether there is an eqality (0), greater than (1) or less than (-1), as in Mathematica's LinearProgramming."

ProcessCols::usage="ProcessCols[A,assump,col] takes a tableau A and assumptions assump about any variables involved and processes the columns corresponding to col to output a new Tableau such that the chosen columns have only one non-zero element. If the col argument is dropped, it processes a number of columns equal to the number of constraint rows in the tableau (the number of rows in A minus 1)."

FixArtificialVariables::usage="FixArtificialVariables[A,artificial,assump] takes a tableau A, a list of artificial variables, artificial and a set of assumption assump and outputs a new tableau in which the artificial variables are removed from the basis."

FindBasis::usage="FindBasis[A] takes a Tableau A and outputs a list of the positions of the elements of the basis, i.e., the positions of the 1s in columns that are all 0s except for one 1. ."

NewBasis::usage="Given a basis, a row and a column, NewBasis[basis, row, col] outputs the new basis assuming a pivot on that row and column, where the basis is given in the form of FindBasis[A]."

ExtractValues::usage="ExtractValues[A] takes a Tableau A and outputs a list of pairs comprising the basis variables (the column representing it) and the values they take at the current feasible point."

LPSolve::usage="LPSolve[A,assump] solves the linear programming problem specified by tableau A under assumptions assump with starting row st (by default, set to 2). It outputs final tableau after all pivoting is done in addition to any unresolved assumptions."

LPSolveAssumptions::usage="LPSolveAssumptions[A,assump,st,curr] solves the linear programming problem specified by tableau A under assumptions assump with starting row st (curr can be set to {}, see documentation). Each unresolved assumption is resolved by splitting into both options and the final output is a list, each element of which specifies some constraints on the variables involved and the corresponding optimum value for the problem when those constraints are satisfied."

PhaseI::usage="PhaseI[A, assump] takes a tableau A corresponding to the problem of minimizing c.x subject to Mx=b, x>=0 in the form output by StartTab[c,M,b] and generates a suitable input to PhaseII by running the first phase of the simplex algorithm."

PhaseII::usage="PhaseII[A,assump] takes the output tableau A of PhaseI, drops the irrelevant rows and columns to generate a starting tableau for theoriginal problem which it solves using LPSolve, outputting thefinal tableau and unresolved assumptions if any."

PhaseIIAssumptions::usage="PhaseIIAssumptions[A,assump] takes the output tableau A of PhaseI, drops the irrelevant rows and columns to generate a starting tableau for theoriginal problem which it solves using LPSolveAssumptions, outputting the final list for that command."*)

LPAssumptions::usage="LPAssumptions[c,M,b,assump] solves the linear programming problem specified by c, M and b (see Mathematica's LinearProgramming) subject to assumptions assump.  Any unknown variables (about which assumptions are made) must be in the objective function."


Begin["`Private`"]
(* Note that b must have all entries non-negative before inputting into StartTab *)
StartTab[c_,A_,b_]:=Join[{Insert[-c,0,-1]},Transpose[Join[Transpose[A],{b}]]]

SlackenMix[obj_,M_,b_]:=Module[{cp=obj,Mp=M,bp={},bt=b,i},If[VectorQ[obj]&&MatrixQ[M]&&(VectorQ[b]||MatrixQ[b]),If[Dimensions[bt]=={Dimensions[M][[1]],2},For[i=1,i<=Dimensions[bt][[1]],i++,(* If an element of b is negative, flip the sign of M and the inequality *) If[NumericQ[bt[[i]][[1]]],If[bt[[i]][[1]]<0,bt=ReplacePart[bt,i->-bt[[i]]];Mp=ReplacePart[Mp,i->-Mp[[i]]]],Print["SlackenMix error: The constraint vector contains values that are not numeric."];Break[]]];Mp=Transpose[Mp];For[i=1,i<=Dimensions[b][[1]],i++,bp=Insert[bp,bt[[i]][[1]],-1];If[bt[[i]][[2]]==1||bt[[i]][[2]]==-1,cp=Insert[cp,0,-1];Mp=Insert[Mp,-bt[[i]][[2]]*UnitVector[Dimensions[bt][[1]],i],-1]]];Mp=Transpose[Mp],If[Dimensions[bt]=={Dimensions[M][[1]]},{cp,Mp,bp}=SlackenMix[obj,M,Thread[{b,1}]],Print["SlackenMix error: third argument has wrong dimensions"];Return[{Null,Null,Null}]]],Print["SlackenMix error: invalid input"];Return[{Null,Null,Null}]];{cp,Mp,bp}]

ProcessCols[A_,assump_,coll1_:Null]:=Module[{Tab,col,row,j,k,dimc,dimr,notdone,colmax,coll=coll1},If[coll1===Null,coll=Dimensions[A][[1]]-1];Tab=A;{dimr,dimc}=Dimensions[Tab];notdone=Table[i,{i,2,dimr}];If[Dimensions[coll]=={},colmax=coll;For[col=1,col<=colmax,col++,If[Simplify[Max[Transpose[Tab][[col]]*ReplacePart[Table[0,{i,1,dimr}],Thread[notdone->1]]]<=0,assump],colmax++,row=Min[notdone];For[j=2,j<=dimr,j++,If[Simplify[Tab[[row,col]]==0,assump],row=j,If[MemberQ[notdone,row]&&Simplify[Tab[[j,col]]!=0,assump]&&Simplify[(Tab[[j,dimc]]/Tab[[j,col]]-Tab[[row,dimc]]/Tab[[row,col]])<0,assump],row=j]]];notdone=DeleteCases[notdone,row];Tab=Simplify[ReplacePart[Tab,row->Tab[[row]]/Tab[[row,col]]]];For[j=1,j<=dimr,j++,If[j!=row&&Simplify[Tab[[row,col]]!=0,assump],Tab=Simplify[ReplacePart[Tab,j->Tab[[j]]-Tab[[row]]*Tab[[j,col]]/Tab[[row,col]]]]]]]],For[k=1,k<=Dimensions[coll][[1]],k++,
col=coll[[k]];If[Simplify[Max[Transpose[Tab][[col]]*ReplacePart[Table[0,{i,1,dimr}],Thread[notdone->1]]]<=0,assump],Print["ProcessCols: Can't do column ",col];Break[],row=Min[notdone];For[j=2,j<=dimr,j++,If[Simplify[Tab[[row,col]]==0,assump],row=j,If[MemberQ[notdone,row]&&Simplify[Tab[[j,col]]!=0,assump]&&Simplify[(Tab[[j,dimc]]/Tab[[j,col]]-Tab[[row,dimc]]/Tab[[row,col]])<0,assump],row=j]]];notdone=DeleteCases[notdone,row];Tab=ReplacePart[Tab,row->Tab[[row]]/Tab[[row,col]]];For[j=1,j<=dimr,j++,If[j!=row&&Simplify[Tab[[row,col]]!=0,assump],Tab=ReplacePart[Tab,j->Tab[[j]]-Tab[[row]]*Tab[[j,col]]/Tab[[row,col]]]]]]]];Tab]

FixArtificialVariables[A_,artificial_,assump_]:=Module[{Tab,inbasis,art,i,j,pos,row,col,dimr,dimc,warn=0},Tab=A;inbasis=FindBasis[Tab];{dimr,dimc}=Dimensions[Tab];art=Intersection[artificial,Transpose[inbasis][[2]]];For[i=1,i<=Dimensions[art][[1]],i++,pos=Cases[inbasis,{_,art[[i]]}];If[Dimensions[pos][[1]]!=1,Print["FixArtificialVariables Error: repeated basis"],row=pos[[1]][[1]];
(* check if row is empty apart from basis element. If so there is a trivial constraint, so do nothing; otherwise move into the basis *)
If[Drop[Tab[[row]],{art[[i]]}]!=0*Drop[Tab[[row]],{art[[i]]}],
For[j=1,j<=dimc-1,j++,If[j!=art[[i]]&&Simplify[Tab[[row,j]],assump]!=0&&!MemberQ[artificial,j],Break[]]];col=j;
(* The next warning may cause PhaseI to fail.  If so, there is a separate error printed by PhaseI *)
If[Tab[[row]][[-1]]!=0&&Tab[[1]][[col]]!=0&&col!=dimc&&warn==0,warn=1;Print["FixArtificialVariables Warning: final column of basis row is non-zero and equals ",Tab[[row]][[-1]],", while the first row of new basis column is also non-zero and equals ",Tab[[1]][[col]],"."]];(*if col\[Equal]dimc then the only replacement is with another artificial variable *)
If[col!=dimc,Tab=ReplacePart[Tab,row->Simplify[Tab[[row]]/Tab[[row,col]],assump]];For[j=1,j<=dimr,j++,If[j!=row,Tab=ReplacePart[Tab,j->Simplify[Tab[[j]]-Tab[[row]]*Tab[[j,col]]/Tab[[row,col]],assump]]]],Print["FixArtificialVariables Warning: can only replace with artificial"]]]]];Tab];

Options[FindBasis]={st->2,IgnoreFirst->False};
FindBasis[A_,OptionsPattern[]]:=Module[{dimr,dimc,i,j,out={},row,col,col1},{dimr,dimc}=Dimensions[A];For[i=OptionValue[st],i<=dimr,i++,row=A[[i]];For[j=1,j<=dimc,j++,If[row[[j]]==1,col=Transpose[A][[j]];col1=Drop[col,{i}];If[OptionValue[IgnoreFirst],col1=Drop[col1,OptionValue[st]-1]];If[col1==0*col1,out=Insert[out,{i,j},-1]]]]];out]

NewBasis[basis_,row_,col_]:=Module[{els,pos,leaving},els=Cases[basis,{row,_}];If[Dimensions[els][[1]]!=1,Print["NewBasis: error when called with basis ",basis," row=",row," and col="col ". Found els=",els],leaving=els[[1]][[2]];pos=Tr[Position[basis,{row,_}]];{leaving,ReplacePart[basis,pos->{row,col}]}]]

Options[ExtractValues]={st->2};
ExtractValues[A_,OptionsPattern[]]:=Module[{dimr,dimc,i,j,out={},col,col1},{dimr,dimc}=Dimensions[A];For[i=1,i<=dimc,i++,col=Transpose[A][[i]];For[j=OptionValue[st],j<=dimr,j++,If[col[[j]]==1,col1=Drop[Drop[col,{j}],OptionValue[st]-1];If[col1==0*col1,out=Insert[out,{i,A[[j]][[-1]]},-1]]]]];out]

(* FindVector takes a final Tableau and outputs the vector corresponding to the optimum *)
FindVector[A_]:=Module[{out,repls},out=ConstantArray[0,Dimensions[A][[2]]-1];repls=Transpose[ExtractValues[A]];ReplacePart[out,Thread[repls[[1]]->repls[[2]]]]]

(* artificial stores the columns of the artificial variables that remain. Inbasis are the rows containing basis variables along with the number of the variable currently in the basis *)
Options[LPSolve]={st->2,ArtificialVars->{},Iterations->50000};
LPSolve[A_,assump_,OptionsPattern[]]:=Module[{col,row,j,it=1,Tab=A,dimr,dimc,ones,art,inbasis,val1,val2,pivoting,left={},leaving},art=OptionValue[ArtificialVars];inbasis=FindBasis[Tab];{dimr,dimc}=Dimensions[Tab];pivoting=Table[i,{i,1,dimc-1}];While[it<OptionValue[Iterations],it++;For[col=1,col<=dimc-1,col++,(* look for a positive entry in the first row to be the pivot column, but don't pivot on artificial variables if they have left the basis *)If[Simplify[Tab[[1,col]]>0,assump]&&!MemberQ[left,col],Break[]]];
(* If a positive entry has not been found exit *)
If[col==dimc,Break[]];
(* Look for a positive entry in the pivot column ignoring the rows before st *)
For[row=OptionValue[st],row<=dimr,row++,If[Simplify[Tab[[row,col]]>0,assump],Break[]]];If[row==dimr+1,Print["LPSolve Error 1"]];
(* look for another positive entry and compare the ratio *)
For[j=row+1,j<=dimr,j++,If[Simplify[Tab[[row,col]]==0,assump],row=j;Print["LPSolve error 2"],If[Simplify[Tab[[j,col]]>0,assump],val1=Simplify[Tab[[j,dimc]]/Tab[[j,col]],assump];val2=Simplify[Tab[[row,dimc]]/Tab[[row,col]]];If[Simplify[val1-val2<0,assump],row=j,If[Simplify[val1-val2==0,assump],(* in the event of a tie, select an artificial variable if possible *)leaving=NewBasis[inbasis,row,col][[1]];If[MemberQ[OptionValue[ArtificialVars],leaving],row=j]]]]]];
(* Replace the chosen row *)
Tab=ReplacePart[Tab,row->Simplify[Tab[[row]]/Tab[[row,col]]]];{leaving,inbasis}=NewBasis[inbasis,row,col];art=Complement[art,{leaving}];If[MemberQ[art,leaving],left=Insert[left,leaving,-1]];
(* Replace the other rows with non-zero elements in chosen column *)For[j=1,j<=dimr,j++,If[j!=row,Tab=ReplacePart[Tab,j->Simplify[Tab[[j]]-Tab[[row]]*Tab[[j,col]]/Tab[[row,col]]]]]]];If[it==OptionValue[Iterations],Print["LPSolve: Optimum not found after ",OptionValue[Iterations]," Iterations."]];If[art==={},,Tab=FixArtificialVariables[Tab,OptionValue[ArtificialVars],assump]];ones=DeleteDuplicates[Simplify[Tab[[1]]]];
For[j=1,j<=Dimensions[ones][[1]],j++,If[Simplify[ones[[j]]<=0,assump],,,Print[ones[[j]]]]];Tab]

(* Debugging\[Rule]{it1,it2} stores all the Tableaus between it1 and it2 in temptab[it1], ..., temptab[it2]. *)
Options[LPSolveAssumptions]={Iterations->50000,  PrintTemp->False, OutputValues->False,OutLength->-1,Debugging->{0,0}(*,CheckCycleLength\[Rule]50*)};
LPSolveAssumptions[A_,assump_,st_,current_,OptionsPattern[]]:=Module[{col,row,i,j,it,br=0,Tab,dimr,dimc,ones,extra={},cur=current,nf=0,oldtab,inbasis,leaving1,leaving2},Tab=A;{dimr,dimc}=Dimensions[Tab];it=1;While[it<OptionValue[Iterations],it++;(*If[it>OptionValue[CheckCycleLength],For[i=1,i\[LessEqual]OptionValue[CheckCycleLength],i++,If[Tab\[Equal]oldtab[i],Print["LPSolveAssumptions: Cycling with cycle length ",Mod[it-i,OptionValue[CheckCycleLength]],"...will not terminate."];Print["Reached iteration ",it,". Current Tableau is stored in temptab123654"];temptab123654=Tab;br=1;Break[]]]];If[br\[Equal]1,Break[]];oldtab[1+Mod[it-1,OptionValue[CheckCycleLength]]]=Tab;*)For[col=1,col<=dimc-1,col++,If[Simplify[Tab[[1,col]]>0,assump],Break[]]];If[col==dimc,Break[]];For[row=st,row<=dimr,row++,If[Simplify[Tab[[row,col]]>0,assump],Break[]]];If[row==dimr+1,nf=1;Print["LPSolveAssumptions: Not found positive entry in column ",col,": ",Transpose[Tab][[col]]];Break[]];inbasis=FindBasis[Tab];For[j=row+1,j<=dimr,j++,If[Simplify[Tab[[row,col]]==0,assump],Print["LPSolveAssumptions: error 2"];row=j,If[Simplify[Tab[[j,col]]>0,assump]&&Simplify[(Tab[[j,dimc]]/Tab[[j,col]]-Tab[[row,dimc]]/Tab[[row,col]])<0,assump],row=j,
If[Simplify[Tab[[j,col]]>0,assump]&&Simplify[(Tab[[j,dimc]]/Tab[[j,col]]-Tab[[row,dimc]]/Tab[[row,col]])==0,assump],(* In event of a tie choose smallest numbered leaving variable to avoid cycles *)leaving1=NewBasis[inbasis,row,col][[1]];leaving2=NewBasis[inbasis,j,col][[1]];If[leaving2<leaving1,row=j]]
]]];Tab=ReplacePart[Tab,row->Simplify[Tab[[row]]/Tab[[row,col]]]];For[j=1,j<=dimr,j++,If[j!=row,Tab=ReplacePart[Tab,j->Simplify[Tab[[j]]-Tab[[row]]*Tab[[j,col]]/Tab[[row,col]]]]]];If[OptionValue[Debugging][[1]]<=it<=OptionValue[Debugging][[2]],temptab[it]=Tab]];If[it==OptionValue[Iterations],Print["LPSolveAssumptions: Optimum not found after ",OptionValue[Iterations] ," iterations."]];If[nf==1,cur=Insert[cur,{assump,\[Infinity]},-1],ones=DeleteDuplicates[Simplify[Tab[[1]]]];
For[j=1,j<=Dimensions[ones][[1]],j++,If[Simplify[ones[[j]]<=0,assump],,,extra=Insert[extra,ones[[j]],-1]]];If[extra=={},If[OptionValue[OutputValues],cur=Insert[cur,{assump,Tab[[1,-1]]},-1],cur=Insert[cur,{assump,If[OptionValue[OutLength]==-1,FindVector[Tab],Take[FindVector[Tab],OptionValue[OutLength]]]},-1]],If[OptionValue[PrintTemp],PrintTemporary["Assumption on ",extra[[1]]]];cur=LPSolveAssumptions[Tab,Insert[assump,extra[[1]]>0,-1],st,cur,{Iterations-> OptionValue[Iterations], PrintTemp-> OptionValue[PrintTemp],OutputValues->OptionValue[OutputValues],OutLength->OptionValue[OutLength]}];cur=LPSolveAssumptions[Tab,Insert[assump,extra[[1]]<0,-1],st,cur,{Iterations-> OptionValue[Iterations], PrintTemp-> OptionValue[PrintTemp],OutputValues->OptionValue[OutputValues],OutLength->OptionValue[OutLength]}]]];cur]

AddId[A_]:=Module[{Tab,cl,Ap},cl=Transpose[A][[-1]];Ap=Drop[Transpose[A],-1];Transpose[Join[Join[Ap,Transpose[Join[{Table[0,{i,1,Dimensions[A][[1]]-1}]},IdentityMatrix[Dimensions[A][[1]]-1]]]],{cl}]]]

Options[PhaseI]={Iterations-> 50000};
PhaseI[A_,assump_,OptionsPattern[]]:=Module[{Tab,Ap,out},Ap=AddId[A];Ap=Join[{Insert[Join[Table[0,{i,1,Dimensions[A][[2]]-1}],Table[-1,{i,1,Dimensions[A][[1]]-1}]],0,-1]},Ap];Tab=ProcessCols[Ap,assump,Table[i,{i,Dimensions[A][[2]],Dimensions[Ap][[2]]-1}]];out=LPSolve[Tab,assump,{st-> 3,ArtificialVars->Table[i,{i,Dimensions[A][[2]],Dimensions[Ap][[2]]-1}]},Iterations-> OptionValue[Iterations]];If[Simplify[out[[1,-1]],assump]!=0,Print["PhaseI failed: original problem may be infeasible"]];out]

Options[PhaseII]={Iterations-> 50000};
PhaseII[A_,assump_,OptionsPattern[]]:=LPSolve[Transpose[Drop[Transpose[Drop[A,1]],{Dimensions[A][[2]]-Dimensions[A][[1]]+2,Dimensions[A][[2]]-1}]],assump,Iterations-> OptionValue[Iterations]]

(* OutputValues\[Rule]True gives the values of the optima, rather than the vector achieving them *)
Options[PhaseIIAssumptions]={Iterations-> 50000, PrintTemp->False,OutputValues->False,OutLength->-1,Debugging->{0,0}(*,CheckCycleLength\[Rule]50*)};
PhaseIIAssumptions[A_,assump_,OptionsPattern[]]:=LPSolveAssumptions[Transpose[Drop[Transpose[Drop[A,1]],{Dimensions[A][[2]]-Dimensions[A][[1]]+2,Dimensions[A][[2]]-1}]],assump,2,{},{Iterations-> OptionValue[Iterations], PrintTemp-> OptionValue[PrintTemp],OutputValues->OptionValue[OutputValues],Debugging->OptionValue[Debugging](*,CheckCycleLength\[Rule]OptionValue[CheckCycleLength]*),OutLength->OptionValue[OutLength]}]

Options[LPAssumptions]={Iterations-> 50000, PrintTemp->False,OutputValues->False,Debugging->{0,0}(*,CheckCycleLength\[Rule]50*)};
LPAssumptions[c_,M_,b_,assump:Except[_?OptionQ]:{},OptionsPattern[]]:=Module[{cp,Mp,bp,i,phase1out},{cp,Mp,bp}=SlackenMix[c,M,b];If[cp===Null,Return[]];phase1out=PhaseI[StartTab[cp,Mp,bp],assump,Iterations->OptionValue[Iterations]];If[OptionValue[PrintTemp],PrintTemporary["Phase I finished."]];PhaseIIAssumptions[phase1out,assump,{Iterations->OptionValue[Iterations], PrintTemp->OptionValue[PrintTemp],Debugging->OptionValue[Debugging],OutputValues->OptionValue[OutputValues](*,CheckCycleLength\[Rule]OptionValue[CheckCycleLength]*),OutLength->Dimensions[c][[1]]}]]






End[ ]

EndPackage[ ]



