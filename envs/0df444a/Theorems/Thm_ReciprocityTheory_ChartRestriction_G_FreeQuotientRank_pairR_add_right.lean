-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_pairR_add_right
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.pairR_add_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:22:40.177792+00:00
-- url     : https://prove2.me/theorems/87558067-4139-47de-905f-1d6d5b5489ef
-- title:
--   Free Quotient Rank: pair R add right
-- statement:
--   The Free Quotient Rank construction uses the pair R add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BetaPf.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BetaPf.lean#L22-L24

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.pairR_add_right {f : ℕ} (u v w : Fin f → ℝ) : pairR u (v + w) = pairR u v + pairR u w := by sorry
