-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_dephased_two_circle_decision
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.dephased_two_circle_decision
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:38:58.121194+00:00
-- url     : https://prove2.me/theorems/369fa5d4-0cf8-43d3-8be8-867ac6cb0f0a
-- title:
--   V B 2: common dephasing of both circles preserves individual optimality
-- statement:
--   For the distinct uniformly phased qubit circles of the preceding example, fix the same dephasing channel $\mathcal N_r(\rho)=(1-r)\rho+rZ\rho Z$, $0<r<1$, for both branches. For any $n\ge1$ and any POVM $M$, there is a computational-basis POVM followed by stochastic processing, described by $N$, with
--   $$\frac1{2\pi}\int_0^{2\pi}\operatorname{tr}(M(B)\mathcal N_r(\psi(\theta,b))^{\otimes n})\,d\theta
--   =\operatorname{tr}(N(B)D_b^{\otimes n})$$
--   for each branch and measurable $B$, where $D_b=\operatorname{diag}(\cos^2(\alpha_b/2),\sin^2(\alpha_b/2))$. This is the concrete sufficiency example, independent of the source’s incorrect universal channel classification.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 24, V B 2: common dephasing of both circles preserves individual optimality

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

/-- PDF p.24: the same dephasing is applied to both circles, with 0<r<1.
This is a valid example, independently of the incorrect universal channel
classification on that page. -/
theorem dephased_two_circle_decision {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) (a : Fin 2 → ℝ)
    (ha : ∀ b, 0 ≤ a b ∧ a b < Real.pi) (hne : a 0 ≠ a 1)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (M : Measurements.OperatorPOVM (Fin n → Fin 2) O) :
    ∃ N : Measurements.OperatorPOVM (Fin n → Fin 2) O, BasisProcessing n N ∧
      ∀ b : Fin 2, ∀ B, MeasurableSet B →
        phaseAverage (fun theta => effectProb (M.operator B)
          (piKron n (phaseFlipMixture r (circleDensity (a b) theta)))) =
          effectProb (N.operator B) (piKron n (circleDiagonal (a b))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
