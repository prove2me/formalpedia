-- Prove2me | Theorems.Thm_TDLC_bxor_assoc
-- name    : TDLC.bxor_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:40.494728+00:00
-- url     : https://prove2.me/theorems/f48f3fcf-58ce-5dc8-8128-947062620081
-- title:
--   TDLC: bxor assoc
-- statement:
--   The TDLC construction uses the bxor assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L712-L713
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L712-L713

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.bxor_assoc (a b c : Bool) : bxor (bxor a b) c = bxor a (bxor b c) := by sorry
