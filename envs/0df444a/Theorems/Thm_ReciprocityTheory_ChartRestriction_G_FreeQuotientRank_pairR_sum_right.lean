-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_pairR_sum_right
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.pairR_sum_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:32.264863+00:00
-- url     : https://prove2.me/theorems/aeeba742-34da-59ec-b2ab-e7596724703d
-- title:
--   Free Quotient Rank: pair R sum right
-- statement:
--   The Free Quotient Rank construction uses the pair R sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BetaPf.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BetaPf.lean#L7-L11

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.pairR_sum_right {f : ℕ} {ι : Type*} (s : Finset ι) (v : Fin f → ℝ) (g : ι → ℝ)
    (w : ι → Fin f → ℝ) : pairR v (∑ j ∈ s, g j • w j) = ∑ j ∈ s, g j * pairR v (w j) := by sorry
