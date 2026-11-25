-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_RB_span_flag
-- name    : ReciprocityTheory.ChartRestriction.G.H1.RB.span_flag
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:11.037409+00:00
-- url     : https://prove2.me/theorems/e40e9b41-e6cc-4048-b93d-7b858e63d951
-- title:
--   RB: span flag
-- statement:
--   The RB construction uses the span flag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SpanFlag.lean#L139-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SpanFlag.lean#L139-L197

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IndepOfFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SpanFlag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.RB
open Finset InnerProductSpace Submodule Module ReciprocityTheory.ReducedBases.T2
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem ReciprocityTheory.ChartRestriction.G.H1.RB.span_flag {d : ℕ} (u : Fin d → E) (hu : LinearIndependent ℝ u) (X : Submodule ℤ E)
    (b : Fin d → E) (hbX : ∀ k, b k ∈ X) (hbV : ∀ k : Fin d, b k ∈ V u (k.val + 1))
    (hb0 : ∀ k, 0 < phi u k (b k)) (hb1 : ∀ k, phi u k (b k) ≤ 1)
    (hbmin : ∀ k : Fin d, ∀ x ∈ X, x ∈ V u (k.val + 1) → 0 < phi u k x → phi u k x ≤ 1 →
      phi u k (b k) ≤ phi u k x) :
    ∀ n ≤ d, ∀ x ∈ X, x ∈ V u n → x ∈ span ℤ (Set.range b) := by sorry
