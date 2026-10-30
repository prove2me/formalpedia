-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_single_observable_estimation
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.single_observable_estimation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:36:47.365136+00:00
-- url     : https://prove2.me/theorems/98623425-c0cc-4939-a2d9-c6e82f2d12ba
-- title:
--   V B 1: the generalized single-observable estimation result
-- statement:
--   Let $H$ be Hermitian on $\mathbb C^d$, $d,n\ge1$, and $\mathcal A=\operatorname{Alg}(H,I)$. In every experiment satisfying the invariant-prior and invariant-parameter hypotheses of Theorem 11 or 13, including its channel and distortion conditions, a fixed spectral measurement of $H$ on each copy followed by stochastic classical processing simulates any POVM at the level
--   $$q_M(B\mid s\in\Delta)=q_{M'}(B\mid s\in\Delta).$$
--   This preserves all parameter-dependent attainable performance values. For mixed distorted priors the actual gauge-invariance condition is retained; nonlinear moments are not assumed to depend only on the algebra reduction.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 22, V B 1: the generalized single-observable estimation result

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

/-- PDF p.22, V B 1: single-observable estimation, including distorted
mixed priors. Nonlinear moments require the actual gauge invariance hypothesis. -/
theorem single_observable_estimation [Nonempty I] {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) {l : ℕ} (H : Mat I) (hH : H.IsHermitian)
    (p : EstimationPrior I l) (E : Mat (Fin n → I) → Mat (Fin n → I))
    (h : EstimationAssumptions (observableAlgebra H : Set (Mat I)) n p E) :
    ∃ S : GeneratorSpectralPVM (observableAlgebra H), ∀ M : Measurements.OperatorPOVM (Fin n → I) O,
      ∃ N : Measurements.OperatorPOVM (Fin n → I) O,
        (∃ K : (Fin n → Fin S.count) → Measure O, Postprocess S K N.operator) ∧
        EquallyInformative p (E ∘ piKron n) M.operator N.operator := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
