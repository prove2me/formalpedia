-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_Tent_add_int_eq_zero_of_notMem
-- name    : ReciprocityTheory.Cheb.Tent_add_int_eq_zero_of_notMem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:47:10.703885+00:00
-- url     : https://prove2.me/theorems/59b0e857-6577-5773-87a7-45d4ea4f12ab
-- title:
--   Cheb: Tent add int eq zero of not Mem
-- statement:
--   The Cheb construction uses the Tent add int eq zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L101-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L101-L107

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

theorem ReciprocityTheory.Cheb.Tent_add_int_eq_zero_of_notMem [DecidableEq ι] (y : ι → ℝ) {n : ι → ℤ}
    (hn : n ∉ Fintype.piFinset fun i => ({-⌊y i⌋, -⌊y i⌋ - 1} : Finset ℤ)) :
    Tent (fun i => y i + n i) = 0 := by sorry
