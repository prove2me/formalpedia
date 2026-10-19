-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P13_remark19_minimising_selections_compact
-- name    : QAlgorithms.Papers.Independent.Dependency50.P13.remark19_minimising_selections_compact
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:15:51.776982+00:00
-- url     : https://prove2.me/theorems/3a97ea22-c6da-4e04-acd3-d2b774574901
-- title:
--   Remark 19: compactness of minimising selections without faithfulness
-- statement:
--   Let H be a nonzero separable complex Hilbert space and F a nonempty convex state set with compact-test weak* closed cone. Suppose rho_n tends in trace norm to rho and D_F(rho_n) tends to the finite value D_F(rho). For any choices sigma_n in Sigma_F(rho_n),
--
--   $$ \overline{\{\sigma_n:n\in\mathbb N\}}^{\|\cdot\|_1}\ \text{is compact},\qquad \operatorname{Cluster}(\sigma_n)\subseteq\Sigma_F(\rho). $$
--
--   No faithfulness assumption is required. Cluster points refer to the sequence along n tending to infinity, rather than to isolated early terms in its range.
--
--   This is the compactness conclusion that remains when uniqueness is unavailable.
-- source:
--   Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme, arXiv:2105.08091v3, PDF p. 18, Remark 19: compactness of minimising selections without faithfulness

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P13

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Remark 19, arXiv:2105.08091v3, PDF p.18.
Without requiring faithfulness, selections are relatively compact and every cluster point
minimizes at the limit state. The finite limiting resource value is retained. -/
theorem remark19_minimising_selections_compact [Nontrivial H] [TopologicalSpace.SeparableSpace H] {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (F : Set (State b)) (hF : F.Nonempty)
    (hconvex : ConvexStates F) (hcone : WeakStarClosedCone F)
    (rhoSeq : ℕ → State b) (rho : State b) (hrho : TraceTendsto rhoSeq rho)
    (hfinite : resourceDistance F rho < ⊤)
    (hvalues : Tendsto (fun n => resourceDistance F (rhoSeq n)) atTop (nhds (resourceDistance F rho)))
    (sigma : ℕ → State b) (hsigma : ∀ n, sigma n ∈ minimisers F (rhoSeq n)) :
    TraceRelativelyCompact sigma ∧
      ∀ tau : State b, TraceClusterPoint sigma tau → tau ∈ minimisers F rho := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P13

end
