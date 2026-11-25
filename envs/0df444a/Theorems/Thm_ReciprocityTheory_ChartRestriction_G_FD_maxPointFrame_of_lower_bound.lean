-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_maxPointFrame_of_lower_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.maxPointFrame_of_lower_bound
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:42.099109+00:00
-- url     : https://prove2.me/theorems/23d26ce6-f41e-5bbb-9f08-c3b950f5a40e
-- title:
--   FD: max Point Frame of lower bound
-- statement:
--   The FD construction uses the max Point Frame of lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MaxPointFrameOfTransference.lean#L9-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/MaxPointFrameOfTransference.lean#L9-L48

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

theorem ReciprocityTheory.ChartRestriction.G.FD.maxPointFrame_of_lower_bound (h41a : LatticeBoundAtMaximum (E := E)) (h6p1 : OrthonormalChartNormControl (E := E)) :
    FrameAtHalfMaximum (E := E) := by sorry
