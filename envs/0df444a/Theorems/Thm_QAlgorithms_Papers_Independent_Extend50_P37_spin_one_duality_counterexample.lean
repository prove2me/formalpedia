-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_spin_one_duality_counterexample
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.spin_one_duality_counterexample
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:45:34.578468+00:00
-- url     : https://prove2.me/theorems/d0ba4aac-5890-4ec2-997e-adcf395cec8d
-- title:
--   Appendix B: a concrete non-gauge duality counterexample
-- statement:
--   Let $H\subseteq U(3)$ be the spin-one $SU(2)$ image, realized in a Cartesian basis by complexified $SO(3)$, and take two tensor factors. Then $H'$ is the scalar unitary group, $H''=U(3)$ and $H$ is not gauge. With total-spin projectors $P_0,P_1,P_2$,
--   $$\operatorname{Alg}((H')^{\times2},P(S_2))=\operatorname{span}\{\Pi_+,\Pi_-\}
--   \subsetneq\operatorname{Comm}(Q(H))=\operatorname{span}\{P_0,P_1,P_2\}.$$
--   Here $P_1=\Pi_-$, $P_2=\Pi_+-P_0$, and $P_0$ projects onto $\sum_{i=0}^2|ii\rangle/\sqrt3$ in Cartesian coordinates. This is the source’s specific non-gauge counterexample.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 36, Appendix B: a concrete non-gauge duality counterexample

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P37

noncomputable section

open MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Next46.P29 (phaseAverage)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P37.estimationMatrixBorel

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- PDF p.36, Appendix B: the actual spin-one counterexample, including
its three total-angular-momentum projectors and strict inclusion. -/
theorem spin_one_duality_counterexample :
    unitaryCentralizer spinOneGroup = scalarUnitaries (Fin 3) ∧
    unitaryCentralizer (unitaryCentralizer spinOneGroup) = unitaryCentralizer ({1} : Set (Mat (Fin 3))) ∧
    ¬ IsGauge spinOneGroup ∧
    alg (localSet 2 (unitaryCentralizer spinOneGroup) ∪ permutations (Fin 3) 2) =
      {X | ∃ a b : ℂ, X = a • permutationSector (Fin 3) 2 false + b • permutationSector (Fin 3) 2 true} ∧
    Set.centralizer (collectiveImage 2 spinOneGroup) =
      {X | ∃ a b c : ℂ, X = a • spinZero + b • permutationSector (Fin 3) 2 true +
        c • (permutationSector (Fin 3) 2 false - spinZero)} ∧
    alg (localSet 2 (unitaryCentralizer spinOneGroup) ∪ permutations (Fin 3) 2) ⊂
      Set.centralizer (collectiveImage 2 spinOneGroup) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
