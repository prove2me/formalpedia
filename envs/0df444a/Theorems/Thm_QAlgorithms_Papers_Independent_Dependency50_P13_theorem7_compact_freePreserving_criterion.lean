-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P13_theorem7_compact_freePreserving_criterion
-- name    : QAlgorithms.Papers.Independent.Dependency50.P13.theorem7_compact_freePreserving_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:11:43.201083+00:00
-- url     : https://prove2.me/theorems/a6b7aa0c-6a02-44c5-95e6-6a6f401648a9
-- title:
--   Theorem 7: compact free-preserving approximation criterion
-- statement:
--   Let H be a nonzero separable complex Hilbert space and (M_n) a single sequence of compact bounded operators such that M_n psi tends to psi for every vector psi. Let F be a nonempty convex trace-norm closed set of states. Suppose
--
--   $$ M_n\operatorname{cone}(F)M_n^*\subseteq\operatorname{cone}(F)\qquad\text{for every }n. $$
--
--   Then cone(F) is compact-test weak* closed. Moreover, D_F is attained at every state and is lower semicontinuous in trace norm, with infinite values allowed. The M_n need not have finite rank and need not be contractions.
--
--   This is a sufficient approximation criterion for applying the general attainment theorem.
-- source:
--   Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme, arXiv:2105.08091v3, PDF p. 8, Theorem 7: compact free-preserving approximation criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P13

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Theorem 7, arXiv:2105.08091v3, PDF p.8.
One compact approximation sequence works for all F; no finite rank or contraction is assumed. -/
theorem theorem7_compact_freePreserving_criterion [Nontrivial H] [TopologicalSpace.SeparableSpace H] {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (M : ℕ → H →L[ℂ] H)
    (hcompact : ∀ n, IsCompactOperator (M n))
    (hstrong : ∀ x, Tendsto (fun n => M n x) atTop (nhds x))
    (F : Set (State b)) (hF : F.Nonempty) (hconvex : ConvexStates F)
    (hclosed : TraceClosedStates F) (hpreserve : ∀ n, PreservesCone F (M n)) :
    WeakStarClosedCone F ∧
    (∀ rho : State b, ∃ sigma ∈ F,
      resourceDistance F rho = relativeEntropy rho.val sigma.val) ∧
    ResourceLowerSemicontinuous F := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P13

end
