-- Prove2me | Theorems.Thm_TDLC_bxor_false_left
-- name    : TDLC.bxor_false_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:07.223936+00:00
-- url     : https://prove2.me/theorems/54de44cd-fa7f-411a-b6e8-0b875005e154
-- title:
--   TDLC: bxor false left
-- statement:
--   The TDLC construction uses the bxor false left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L701-L701
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L701-L701

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.bxor_false_left (b : Bool) : bxor false b = b := by sorry

attribute [defeq] TDLC.bxor_false_left
