-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_frameAtMaximum_of_transference
-- name    : ReciprocityTheory.ChartRestriction.G.FD.frameAtMaximum_of_transference
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:16:35.887184+00:00
-- url     : https://prove2.me/theorems/4d14b385-a768-5ce0-a6d3-861680d7f839
-- title:
--   FD: frame At Maximum of transference
-- statement:
--   The FD construction uses the frame At Maximum of transference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrameAtMaximumOfTransference.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FrameAtMaximumOfTransference.lean#L9-L10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LatticeBoundAtMaximumOfTransference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlagSpanBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalChartNormControlHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FrameAtMaximumOfTransference
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

theorem ReciprocityTheory.ChartRestriction.G.FD.frameAtMaximum_of_transference (hD5 : CoveringRadiusStatement) : FrameAtMaximum (E := E) := by sorry
