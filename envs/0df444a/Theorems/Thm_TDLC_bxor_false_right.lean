-- Prove2me | Theorems.Thm_TDLC_bxor_false_right
-- name    : TDLC.bxor_false_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:05.462197+00:00
-- url     : https://prove2.me/theorems/b8d6b097-0c91-5b59-bfb3-68586abd9aa1
-- title:
--   TDLC: bxor false right
-- statement:
--   The TDLC construction uses the bxor false right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L703-L704
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L703-L704

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.bxor_false_right (b : Bool) : bxor b false = b := by sorry
