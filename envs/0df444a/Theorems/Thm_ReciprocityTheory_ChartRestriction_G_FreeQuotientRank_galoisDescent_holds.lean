-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_galoisDescent_holds
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.galoisDescent_holds
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:29:12.878404+00:00
-- url     : https://prove2.me/theorems/04c28b65-7617-48e1-bba4-695019e5bab7
-- title:
--   Free Quotient Rank: galois Descent holds
-- statement:
--   The Free Quotient Rank construction uses the galois Descent holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DescPf.lean#L57-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/DescPf.lean#L57-L71

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_DescPf
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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.galoisDescent_holds : GaloisDescentStatement := by sorry
