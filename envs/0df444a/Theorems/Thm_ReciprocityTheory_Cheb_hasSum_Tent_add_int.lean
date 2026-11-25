-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_hasSum_Tent_add_int
-- name    : ReciprocityTheory.Cheb.hasSum_Tent_add_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:48:30.066292+00:00
-- url     : https://prove2.me/theorems/8a4b2d30-530f-4c7c-9156-1ee651cc6069
-- title:
--   Cheb: has Sum Tent add int
-- statement:
--   The Cheb construction uses the has Sum Tent add int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L116-L121

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
variable {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.Cheb.hasSum_Tent_add_int (y : ι → ℝ) : HasSum (fun n : ι → ℤ => Tent (fun i => y i + n i)) 1 := by sorry
