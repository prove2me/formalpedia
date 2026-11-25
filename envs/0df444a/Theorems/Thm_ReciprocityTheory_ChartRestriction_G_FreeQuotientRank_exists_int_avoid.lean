-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_exists_int_avoid
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.exists_int_avoid
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:39.428453+00:00
-- url     : https://prove2.me/theorems/b7eebd2c-9a62-474c-a8f7-f683075e6b0e
-- title:
--   Free Quotient Rank: exists int avoid
-- statement:
--   The Free Quotient Rank construction uses the exists int avoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BetaPf.lean#L30-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/BetaPf.lean#L30-L59

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.exists_int_avoid {f : ℕ} (Z : Finset (Fin f → ℝ)) (hZ : ∀ z ∈ Z, z ≠ 0) :
    ∃ t : Fin f → ℤ, ∀ z ∈ Z, ∑ j, z j * (t j : ℝ) ≠ 0 := by sorry
