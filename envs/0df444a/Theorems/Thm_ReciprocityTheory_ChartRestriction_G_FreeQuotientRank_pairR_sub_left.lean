-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_pairR_sub_left
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.pairR_sub_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:55.712801+00:00
-- url     : https://prove2.me/theorems/75e4bc01-fd1d-47dd-9b4b-a5d4e4775a27
-- title:
--   Free Quotient Rank: pair R sub left
-- statement:
--   The Free Quotient Rank construction uses the pair R sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BetaPf.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BetaPf.lean#L19-L20

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.pairR_sub_left {f : ℕ} (u v w : Fin f → ℝ) : pairR (u - v) w = pairR u w - pairR v w := by sorry
