-- Prove2me | Theorems.Thm_ReciprocityTheory_Cheb_tent_add_int_eq_zero_of_notMem__f19901
-- name    : ReciprocityTheory.Cheb.tent_add_int_eq_zero_of_notMem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:49:15.571803+00:00
-- url     : https://prove2.me/theorems/f1990177-09b5-4da1-a1f6-400a2f5dda2d
-- title:
--   Cheb: tent add int eq zero of not Mem
-- statement:
--   The Cheb construction uses the tent add int eq zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L32-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsProdSubProdLeSumAbsSub.lean#L32-L43

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

theorem ReciprocityTheory.Cheb.tent_add_int_eq_zero_of_notMem (t : ℝ) {n : ℤ} (hn : n ∉ ({-⌊t⌋, -⌊t⌋ - 1} : Finset ℤ)) :
    tent (t + n) = 0 := by sorry
