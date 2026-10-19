-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P13_corollary17_determined_by_finiteRank
-- name    : QAlgorithms.Papers.Independent.Dependency50.P13.corollary17_determined_by_finiteRank
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:14:03.798473+00:00
-- url     : https://prove2.me/theorems/bc130883-b4b6-4af8-8d8f-cefda905da51
-- title:
--   Corollary 17: determination by finite-rank states
-- statement:
--   Let H be a nonzero separable complex Hilbert space and F a nonempty state set with compact-test weak* closed cone. Every state rho admits finite-rank states rho_n such that
--
--   $$ \rho_n\xrightarrow{\|\cdot\|_1}\rho,\qquad D_F(\rho_n)\longrightarrow D_F(\rho)\in[0,+\infty]. $$
--
--   Consequently, if G is another nonempty state set with weak* closed cone and D_F agrees with D_G on every finite-rank state, the two distances agree on every state.
--
--   This makes the source's determination claim explicit, through the spectral-truncation consequence (68). Initial zero-mass projections need not be included, and a finite-rank state permits an eventually constant approximating sequence.
-- source:
--   Attainability and lower semi-continuity of the relative entropy of entanglement, and variations on the theme, arXiv:2105.08091v3, PDF p. 17, Corollary 17: determination by finite-rank states

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P13

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Corollary 17, arXiv:2105.08091v3, PDF p.17, through (68).
Finite-rank approximation recovers the extended value. Thus agreement of admissible resource
distances on finite-rank states determines agreement on every state. -/
theorem corollary17_determined_by_finiteRank [Nontrivial H] [TopologicalSpace.SeparableSpace H] {I : Type*} [Countable I]
    (b : HilbertBasis I ℂ H) (F : Set (State b)) (hF : F.Nonempty)
    (hcone : WeakStarClosedCone F) :
    (∀ rho : State b, ∃ rhoSeq : ℕ → State b,
      (∀ n, FiniteRankState (rhoSeq n)) ∧ TraceTendsto rhoSeq rho ∧
      Tendsto (fun n => resourceDistance F (rhoSeq n)) atTop (nhds (resourceDistance F rho))) ∧
    (∀ G : Set (State b), G.Nonempty → WeakStarClosedCone G →
      (∀ rho : State b, FiniteRankState rho → resourceDistance F rho = resourceDistance G rho) →
      ∀ rho : State b, resourceDistance F rho = resourceDistance G rho) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P13

end
