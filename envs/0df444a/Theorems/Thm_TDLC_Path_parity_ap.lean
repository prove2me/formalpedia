-- Prove2me | Theorems.Thm_TDLC_Path_parity_ap
-- name    : TDLC.Path.parity_ap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:07.672054+00:00
-- url     : https://prove2.me/theorems/f95b2ff8-719e-4ba1-a5ff-245a2543cb3a
-- title:
--   Path: parity ap
-- statement:
--   The Path construction uses the parity ap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L740-L748
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L740-L748

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.Path.parity_ap {A B : Type u} (f : A → B) {x y : A}
    (p : Path x y) : Path.parity (Path.ap f p) = Path.parity p := by sorry
