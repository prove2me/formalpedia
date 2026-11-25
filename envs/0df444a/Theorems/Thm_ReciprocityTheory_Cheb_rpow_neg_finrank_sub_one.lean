-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_rpow_neg_finrank_sub_one
-- name    : ReciprocityTheory.Cheb.rpow_neg_finrank_sub_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:49:34.960623+00:00
-- url     : https://prove2.me/theorems/d2c090f2-050d-5d98-a339-0b2cd9a836d3
-- title:
--   Cheb: rpow neg finrank sub one
-- statement:
--   The Cheb construction uses the rpow neg finrank sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/RpowNegFinrankSubOne.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/RpowNegFinrankSubOne.lean#L16-L18

import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Definitions.Def_ReciprocityTheory_Chebotarev_RpowNegFinrankSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.rpow_neg_finrank_sub_one (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    t ^ (-(n : ℝ) - 1) = (t ^ (n + 1))⁻¹ := by sorry
