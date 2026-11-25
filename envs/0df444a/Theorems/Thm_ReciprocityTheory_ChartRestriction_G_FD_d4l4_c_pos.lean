-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_d4l4_c_pos
-- name    : ReciprocityTheory.ChartRestriction.G.FD.d4l4_c_pos
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:21:51.914247+00:00
-- url     : https://prove2.me/theorems/3a8397fe-aa53-4687-a575-4d59d4ad7a9d
-- title:
--   FD: d4l4 c pos
-- statement:
--   The FD construction uses the d4l4 c pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HolomorphicPeriodicityExtension.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HolomorphicPeriodicityExtension.lean#L11-L14

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Complex Filter Topology
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.d4l4_c_pos {r : ℕ} (X : Data E r) (τ : X.Ψ) : 0 < X.c τ := by sorry
