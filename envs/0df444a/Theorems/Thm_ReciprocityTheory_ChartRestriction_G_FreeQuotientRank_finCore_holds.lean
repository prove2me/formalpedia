-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_finCore_holds
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finCore_holds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:17.022118+00:00
-- url     : https://prove2.me/theorems/dd7051d6-6f6b-4ce0-b025-9da4bc6bdb5d
-- title:
--   Free Quotient Rank: fin Core holds
-- statement:
--   The Free Quotient Rank construction uses the fin Core holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FinCorePf.lean#L7-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FinCorePf.lean#L7-L83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCoreSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DiscPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_UnitPointLiftBall
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCorePf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finCore_holds : FinCoreStatement := by sorry
