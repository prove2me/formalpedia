-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P13_example8_energySet_cone_not_weakStarClosed
-- name    : QAlgorithms.Papers.Independent.Dependency50.P13.example8_energySet_cone_not_weakStarClosed
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:12:39.109399+00:00
-- url     : https://prove2.me/theorems/a1a30d00-fca5-444c-a85e-7c25fd33a7f8
-- title:
--   Example 8: a trace-norm closed free set whose cone is not weak*-closed
-- statement:
--   Identify the source's tensor product of two countably infinite number-basis Hilbert spaces with a Hilbert space having product basis |k,l>. For a state rho let its first-factor number energy be the extended sum sum_{k,l} k<k,l|rho|k,l>. At the energy bound one, set
--
--   $$ F_{N,1}=\left\{\rho\in\mathcal D(H):\sum_{k,l\ge0}k\langle k,l|\rho|k,l\rangle\le1\right\}. $$
--
--   This set is convex and trace-norm closed, but its ray-generated cone is not compact-test weak* closed.
--
--   The assertion is the explicit E=1 counterexample on the page. The printed unrestricted E>=0 wording is corrected because the zero-energy cone is weak* closed. This illustrates the necessity of the free-preservation condition in Theorem 7.
-- source:
--   Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme, arXiv:2105.08091v3, PDF p. 8, Example 8: a trace-norm closed free set whose cone is not weak*-closed

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P13

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Example 8, arXiv:2105.08091v3, PDF p.8, at E=1, as actually proved on that page.
The printed nonclosedness for all E>=0 fails at E=0. Product-basis coordinates identify
H with the source's countable tensor-product space. Independent moderation is required. -/
theorem example8_energySet_cone_not_weakStarClosed [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (b : HilbertBasis (ℕ × ℕ) ℂ H) :
    ConvexStates (numberEnergyFreeSet b) ∧ TraceClosedStates (numberEnergyFreeSet b) ∧
    ¬ WeakStarClosedCone (numberEnergyFreeSet b) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P13

end
