-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlagSpanBounds_span_le_of_upper
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.span_le_of_upper
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:14:42.009227+00:00
-- url     : https://prove2.me/theorems/74556e98-0038-4494-b34f-75433635ce12
-- title:
--   Flag Span Bounds: span le of upper
-- statement:
--   The Flag Span Bounds construction uses the span le of upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlagSpanBounds.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlagSpanBounds.lean#L11-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearMaximumHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlagSpanBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.span_le_of_upper (p : ℕ) (hp : p ≤ r) (M N : Matrix (Fin r) (Fin r) ℂ) (hN : N.BlockTriangular id) :
    Submodule.span ℂ (Set.range fun a : Fin p => col (M * N) (Fin.castLE hp a)) ≤
      Submodule.span ℂ (Set.range fun a : Fin p => col M (Fin.castLE hp a)) := by sorry
