-- Prove2me | Theorems.Thm_TDLC_bxor_comm
-- name    : TDLC.bxor_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:08.355201+00:00
-- url     : https://prove2.me/theorems/95f2aa9c-0810-4620-9a6b-f0e2b60e1d67
-- title:
--   TDLC: bxor comm
-- statement:
--   The TDLC construction uses the bxor comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L709-L710
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L709-L710

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.bxor_comm (a b : Bool) : bxor a b = bxor b a := by sorry
