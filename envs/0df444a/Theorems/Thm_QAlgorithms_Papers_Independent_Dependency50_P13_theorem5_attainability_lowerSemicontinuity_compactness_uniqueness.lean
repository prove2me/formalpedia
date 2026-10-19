-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P13_theorem5_attainability_lowerSemicontinuity_compactness_uniqueness
-- name    : QAlgorithms.Papers.Independent.Dependency50.P13.theorem5_attainability_lowerSemicontinuity_compactness_uniqueness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:10:57.547981+00:00
-- url     : https://prove2.me/theorems/59be3fcb-4c45-4338-8b3a-6f3dee759adf
-- title:
--   Theorem 5 (seed): attainability, lower semicontinuity, compactness and uniqueness
-- statement:
--   Let H be a nonzero separable complex Hilbert space and F a nonempty set of density operators whose ray-generated cone is compact-test weak* closed. Define D_F(rho)=inf_{sigma in F} D(rho||sigma) in [0,infinity], using natural logarithms. Then
--
--   $$ \forall\rho\in\mathcal D(H)\;\exists\sigma\in F:\quad D_F(\rho)=D(\rho\|\sigma), $$
--
--   and D_F is lower semicontinuous in the trace norm. If D_F(rho)<infinity, the minimizer set Sigma_F(rho) is nonempty and trace-norm compact. It is convex when F is convex, and contains exactly one state when F is convex and rho has zero kernel. No convexity is required for the first two assertions.
--
--   This gives attainment, regularity, compactness, and the precise finite-value and faithfulness conditions for uniqueness.
-- source:
--   Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme, arXiv:2105.08091v3, PDF p. 7, Theorem 5 (seed): attainability, lower semicontinuity, compactness and uniqueness

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P13

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Theorem 5, arXiv:2105.08091v3, PDF p.7, all four clauses.
Nonemptiness is the proof's convention on p.9. Only (c),(d) require finite distance. -/
theorem theorem5_attainability_lowerSemicontinuity_compactness_uniqueness [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    {I : Type*} [Countable I] (b : HilbertBasis I ℂ H)
    (F : Set (State b)) (hF : F.Nonempty) (hcone : WeakStarClosedCone F) :
    (∀ rho : State b, ∃ sigma ∈ F,
      resourceDistance F rho = relativeEntropy rho.val sigma.val) ∧
    ResourceLowerSemicontinuous F ∧
    (∀ rho : State b, resourceDistance F rho < ⊤ →
      (minimisers F rho).Nonempty ∧ TraceCompactStates (minimisers F rho) ∧
      (ConvexStates F → ConvexStates (minimisers F rho)) ∧
      (ConvexStates F → Function.Injective rho.val.val → ∃! sigma : State b, sigma ∈ minimisers F rho)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P13

end
