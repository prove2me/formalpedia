-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_finiteDetect_holds
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finiteDetect_holds
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:04.716347+00:00
-- url     : https://prove2.me/theorems/1ce42588-4dc6-4e6b-a7de-76b0879d4dfc
-- title:
--   Free Quotient Rank: finite Detect holds
-- statement:
--   The Free Quotient Rank construction uses the finite Detect holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FinDetPf.lean#L5-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FinDetPf.lean#L5-L30

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FiniteDetectStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinDetPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finiteDetect_holds : FiniteDetectStatement := by sorry
