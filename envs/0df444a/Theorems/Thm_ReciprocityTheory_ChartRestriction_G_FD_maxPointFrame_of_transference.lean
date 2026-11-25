-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_maxPointFrame_of_transference
-- name    : ReciprocityTheory.ChartRestriction.G.FD.maxPointFrame_of_transference
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:16:19.313569+00:00
-- url     : https://prove2.me/theorems/9bc78af4-f89b-5fc0-9c82-8b5447643e5f
-- title:
--   FD: max Point Frame of transference
-- statement:
--   The FD construction uses the max Point Frame of transference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MaxPointFrameOfTransference.lean#L50-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MaxPointFrameOfTransference.lean#L50-L50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearHalfMax
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_NonvanishingNearHalfMaxHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FrameAtMaximumOfTransference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MaxPointFrameOfTransference
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.maxPointFrame_of_transference (hD5 : CoveringRadiusStatement) : FrameAtHalfMaximum (E := E) := by sorry
