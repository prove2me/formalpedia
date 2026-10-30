-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P37_performance_values_preserved
-- name    : QAlgorithms.Papers.Independent.Extend50.P37.performance_values_preserved
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:33:49.395994+00:00
-- url     : https://prove2.me/theorems/aace885a-ee33-401d-9ff5-710293ee09d6
-- title:
--   Corollary 15: all parameter-dependent performance values are preserved
-- statement:
--   In an $n$-copy experiment satisfying Theorem 11 or 13 for $\mathcal A$, let $F$ be a real-valued performance functional on normalized POVMs that takes the same value whenever all positive-probability parameter-box conditional outcome laws agree. Then
--   $$\{F(M):M\text{ is a POVM}\}=\{F(M):M\text{ is an }\mathcal A^{\otimes n}\text{-valued POVM}\}.$$
--   In particular any attained optimum has a representative in the local algebra. No optimizer existence assumption is hidden in an infimum or supremum.
-- source:
--   A generalization of Schur-Weyl duality with applications in quantum estimation, arXiv:1112.0638v3, PDF p. 21, Corollary 15: all parameter-dependent performance values are preserved

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

/-- PDF p.21, Corollary 15: every attainable performance value is attained
in the local algebra. This restricts any attained optimum without asserting
existence of an optimizer for an arbitrary functional. -/
theorem performance_values_preserved [Nonempty I] {O : Type*} [MeasurableSpace O]
    (n : ℕ) (hn : 0 < n) {l : ℕ} (A : StarSubalgebra ℂ (Mat I))
    (p : EstimationPrior I l) (E : Mat (Fin n → I) → Mat (Fin n → I))
    (h : EstimationAssumptions (A : Set (Mat I)) n p E)
    (F : Measurements.OperatorPOVM (Fin n → I) O → ℝ)
    (hF : ∀ M N : Measurements.OperatorPOVM (Fin n → I) O, EquallyInformative p (E ∘ piKron n) M.operator N.operator → F M = F N) :
    Set.range F = {v | ∃ M : Measurements.OperatorPOVM (Fin n → I) O,
      InAlgebra M.operator (tensorAlg n (A : Set (Mat I))) ∧ F M = v} := by sorry

end QAlgorithms.Papers.Independent.Extend50.P37

end
