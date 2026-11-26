-- Prove2me | Theorems.Thm_TDLC_Path_parity_inv
-- name    : TDLC.Path.parity_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:07.605218+00:00
-- url     : https://prove2.me/theorems/496959f0-f62f-56a0-a8c9-222f67cd0241
-- title:
--   Path: parity inv
-- statement:
--   The Path construction uses the parity inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L732-L738
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L732-L738

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.Path.parity_inv {A : Type u} {x y : A} (p : Path x y) :
    Path.parity (Path.inv p) = Path.parity p := by sorry
