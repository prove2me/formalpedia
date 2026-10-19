-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P13_proposition18_unique_minimiser_continuity
-- name    : QAlgorithms.Papers.Independent.Dependency50.P13.proposition18_unique_minimiser_continuity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:14:54.791876+00:00
-- url     : https://prove2.me/theorems/36ecd899-9b69-4578-8c9e-dbc31a2ce3d4
-- title:
--   Proposition 18: continuity of the unique minimiser
-- statement:
--   Let H be a nonzero separable complex Hilbert space, and let F be nonempty and convex with compact-test weak* closed cone. Suppose rho_n tends in trace norm to a faithful state rho, meaning ker rho={0}, and
--
--   $$ D_F(\rho_n)\longrightarrow D_F(\rho)<+\infty. $$
--
--   For every selection sigma_n in Sigma_F(rho_n), there is a unique tau in Sigma_F(rho) and sigma_n tends to tau in trace norm. The rho_n need not be faithful, and no finite-distance condition is imposed on every early index.
--
--   This identifies continuity of the minimizer under convergence of both states and resource values.
-- source:
--   Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme, arXiv:2105.08091v3, PDF p. 18, Proposition 18: continuity of the unique minimiser

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P13

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Proposition 18, arXiv:2105.08091v3, PDF p.18, (69).
Only the limit state is faithful; early resource values may be infinite. -/
theorem proposition18_unique_minimiser_continuity [Nontrivial H] [TopologicalSpace.SeparableSpace H] {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (F : Set (State b)) (hF : F.Nonempty)
    (hconvex : ConvexStates F) (hcone : WeakStarClosedCone F)
    (rhoSeq : ℕ → State b) (rho : State b) (hrho : TraceTendsto rhoSeq rho)
    (hfaithful : Function.Injective rho.val.val) (hfinite : resourceDistance F rho < ⊤)
    (hvalues : Tendsto (fun n => resourceDistance F (rhoSeq n)) atTop (nhds (resourceDistance F rho)))
    (sigma : ℕ → State b) (hsigma : ∀ n, sigma n ∈ minimisers F (rhoSeq n)) :
    ∃ tau ∈ minimisers F rho,
      (∀ tau2 ∈ minimisers F rho, tau2 = tau) ∧ TraceTendsto sigma tau := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P13

end
