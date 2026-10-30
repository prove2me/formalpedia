-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P36_one_sided_does_not_imply_two_sided
-- name    : QAlgorithms.Papers.Independent.Extend50.P36.one_sided_does_not_imply_two_sided
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:00:10.765137+00:00
-- url     : https://prove2.me/theorems/c8d41303-8f23-43f2-ba1d-f88cc4ba0e99
-- title:
--   Proposition IV.1: sharing on one side does not imply both sides
-- statement:
--   For positive integers $m,n$, a state is $m$-$n$ sharable when a density operator on $H_L^{\otimes m}\otimes H_R^{\otimes n}$ has that same state as every left-right pair marginal. Arbitrary sharing means such an extension exists for every positive finite $m,n$.
--
--   Define the two-qubit density operator $\rho=[(|00\rangle+|11\rangle)(\langle00|+\langle11|)+|10\rangle\langle10|]/3$ and the normalized vector $v=(|000\rangle+|101\rangle+|110\rangle)/\sqrt3$. Then
--   $$\operatorname{Tr}_C|v\rangle\langle v|=\operatorname{Tr}_B|v\rangle\langle v|=\rho,\qquad \rho\text{ is }1\text{-}2\text{ sharable},\quad \rho\text{ is not }2\text{-}2\text{ sharable}.$$
--   This explicit example establishes that the implication fails for general bipartite qubit states.
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, PDF p. 12, Proposition IV.1: sharing on one side does not imply both sides

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Proposition IV.1, PDF pp.12–13: the source's explicit qubit counterexample,
with its specified pure three-party extension. -/
theorem one_sided_does_not_imply_two_sided :
    IsDensityMatrix qubitSharingWitness ∧
    JoinsTwo qubitJoiningWitness qubitSharingWitness qubitSharingWitness ∧
    Sharable 1 2 qubitSharingWitness ∧ ¬ Sharable 2 2 qubitSharingWitness := by sorry

end QAlgorithms.Papers.Independent.Extend50.P36

end
