-- Prove2me | Theorems.Thm_TDLC_Path_parity_concat
-- name    : TDLC.Path.parity_concat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:05.130853+00:00
-- url     : https://prove2.me/theorems/8fabd640-d60f-4bba-9bff-9f6a2fc3e50a
-- title:
--   Path: parity concat
-- statement:
--   The Path construction uses the parity concat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L720-L730
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L720-L730

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.Path.parity_concat {A : Type u} {x y z : A}
    (p : Path x y) (q : Path y z) :
    Path.parity (p ++ₚ q) = bxor (Path.parity p) (Path.parity q) := by sorry
