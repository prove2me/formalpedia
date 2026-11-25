-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_funKer_holds
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.funKer_holds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:14:01.62282+00:00
-- url     : https://prove2.me/theorems/c2ecce96-36b6-4471-8581-b58b0f44977b
-- title:
--   Free Quotient Rank: fun Ker holds
-- statement:
--   The Free Quotient Rank construction uses the fun Ker holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FunKerPf.lean#L49-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FunKerPf.lean#L49-L224

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_RationalityHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FunKerPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
open TensorProduct

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.funKer_holds : FunKerStatement := by sorry
