-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FlagSpanBounds_rho_pos
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.rho_pos
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:18:04.098503+00:00
-- url     : https://prove2.me/theorems/1a8ec2a0-2f70-5ad6-9330-d4308a9033f8
-- title:
--   Flag Span Bounds: rho pos
-- statement:
--   The Flag Span Bounds construction uses the rho pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlagSpanBounds.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlagSpanBounds.lean#L63-L75

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
variable (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.rho_pos {w : ℝ} (hw1 : 1 ≤ w) (hr : 0 < r) : 0 < frameRadius w r ∧ frameRadius w r ≤ 1 / 10 := by sorry
