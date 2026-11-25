-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_sum_tent_add_int_pair
-- name    : ReciprocityTheory.Cheb.sum_tent_add_int_pair
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:49:06.805917+00:00
-- url     : https://prove2.me/theorems/d3f0bfb6-d4a1-52d0-a8ec-d73644aff0eb
-- title:
--   Cheb: sum tent add int pair
-- statement:
--   The Cheb construction uses the sum tent add int pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L45-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L45-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsProdSubProdLeSumAbsSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open ReciprocityTheory ReciprocityTheory.Cheb

theorem ReciprocityTheory.Cheb.sum_tent_add_int_pair (t : ℝ) :
    ∑ n ∈ ({-⌊t⌋, -⌊t⌋ - 1} : Finset ℤ), tent (t + n) = 1 := by sorry
