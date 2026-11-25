-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_sum_Tent_add_int_piFinset
-- name    : ReciprocityTheory.Cheb.sum_Tent_add_int_piFinset
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:48:41.287821+00:00
-- url     : https://prove2.me/theorems/3cfb7f8d-4b97-5499-8e11-7e8aca506d33
-- title:
--   Cheb: sum Tent add int pi Finset
-- statement:
--   The Cheb construction uses the sum Tent add int pi Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L109-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L109-L114

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

theorem ReciprocityTheory.Cheb.sum_Tent_add_int_piFinset [DecidableEq ι] (y : ι → ℝ) :
    ∑ n ∈ Fintype.piFinset (fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)), Tent (fun i => y i + n i) = 1 := by sorry
