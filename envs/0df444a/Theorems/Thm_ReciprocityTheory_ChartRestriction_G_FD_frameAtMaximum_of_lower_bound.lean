-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_frameAtMaximum_of_lower_bound
-- name    : ReciprocityTheory.ChartRestriction.G.FD.frameAtMaximum_of_lower_bound
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:19.598115+00:00
-- url     : https://prove2.me/theorems/52261607-4e1b-4381-b491-dbec5abdd0dd
-- title:
--   FD: frame At Maximum of lower bound
-- statement:
--   The FD construction uses the frame At Maximum of lower bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlagSpanBounds.lean#L85-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlagSpanBounds.lean#L85-L105

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.frameAtMaximum_of_lower_bound (h41a : LatticeBoundAtMaximum (E := E)) (h6p1 : OrthonormalChartNormControl (E := E)) :
    FrameAtMaximum (E := E) := by sorry
