-- Prove2me | Theorems.Thm_TDLC_bxor_self
-- name    : TDLC.bxor_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:04.996984+00:00
-- url     : https://prove2.me/theorems/0e1f726f-b508-4098-a3f8-6192ccb0b5aa
-- title:
--   TDLC: bxor self
-- statement:
--   The TDLC construction uses the bxor self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L706-L707
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L706-L707

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.bxor_self (b : Bool) : bxor b b = false := by sorry
