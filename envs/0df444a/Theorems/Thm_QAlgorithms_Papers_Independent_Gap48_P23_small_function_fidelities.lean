-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_small_function_fidelities
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.small_function_fidelities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:45:34.462876+00:00
-- url     : https://prove2.me/theorems/627bb70f-e3a4-42f6-90d3-d7e3b75ffcce
-- title:
--   §5.1.1–5.1.2: exact optimal fidelities
-- statement:
--   Work in finite-dimensional complex Hilbert spaces with the indicated computational bases. A channel is a fixed completely positive trace-preserving map, independent of the unknown word $x$ and common basis $U$. Write $\rho_x^U=U^{\otimes n}|x\rangle\langle x|U^{\dagger\otimes n}$. For an input promise $P$, let $F_{f,P}(\Phi)$ be the minimum of $\langle f(x)|U^\dagger\Phi(\rho_x^U)U|f(x)\rangle$ over every allowed $x$ and $U\in U(d)$, and let $F_{f,P}$ be its supremum over channels. An omitted $P$ means all words. Boolean functions use $d=2$; positive odd $n$ is imposed whenever symmetry and equivariance of a Boolean function are required.
--
--   For the lower-half truth tables in increasing binary order, the exact optimal fidelity lists at $n=1,3,5,7$ are
--   $$\begin{aligned}n=1:&\ [1,2/3],\\n=3:&\ [8/9,3/5,4/5,29/45],\\n=5:&\ [62/75,4/7,5/7,95/153,124/153,4/7,5/7,331/525],\\n=7:&\ [2888/3675,5/9,2/3,47/78,59/78,5/9,2/3,1141/1845,1444/1845,5/9,2/3,47/78,59/78,5/9,2/3,6841/11025].\end{aligned}$$
--   The six Table 2 parameter vectors are retained as feasible solutions with these optimal objectives. No infinite suffix-pattern claim is included.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 34, §5.1.1–5.1.2: exact optimal fidelities

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF pp.34-35: every literal small-function value; includes attainment and
Table 2 interpolation vectors through their exact feasible optimal solutions. -/
theorem small_function_fidelities :
    (∀ n ∈ ({1,3,5,7} : Finset ℕ), ∀ i : Fin ((smallFidelities n).length),
      optimalFunctionFidelity (fun _ => True) (tableFunction n i.val) = (smallFidelities n).get i) ∧
    FunctionLPFeasible (tableFunction 1 0) 1 (fun _ => 1) ∧
    FunctionLPFeasible (tableFunction 1 1) (2/3) (fun _ => 0) ∧
    FunctionLPFeasible (tableFunction 3 0) (8/9) (fun _ => 1) ∧
    FunctionLPFeasible (tableFunction 3 1) (3/5) (fun k => if k.val = 0 then 1/2 else 0) ∧
    FunctionLPFeasible (tableFunction 3 2) (4/5) (fun k => if k.val = 0 then 0 else 1) ∧
    FunctionLPFeasible (tableFunction 3 3) (29/45) (fun _ => 0) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
