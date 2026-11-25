-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_beta_holds
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.beta_holds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:13:32.643308+00:00
-- url     : https://prove2.me/theorems/51f29d67-d9b5-4384-ae24-692a24502bab
-- title:
--   Free Quotient Rank: beta holds
-- statement:
--   The Free Quotient Rank construction uses the beta holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BetaPf.lean#L61-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BetaPf.lean#L61-L260

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BetaSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_BetaPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Finset

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.beta_holds : BetaStatement := by sorry
