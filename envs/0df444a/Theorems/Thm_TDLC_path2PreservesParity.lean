-- Prove2me | Theorems.Thm_TDLC_path2PreservesParity
-- name    : TDLC.path2PreservesParity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:24:24.449638+00:00
-- url     : https://prove2.me/theorems/ce8cf211-2188-520f-ae35-78f354c57ac8
-- title:
--   TDLC: path2 Preserves Parity
-- statement:
--   Every finite sequence of two-cells preserves structural parity.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L818-L822
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Solution.lean#L818-L822

import Definitions.Def_TDLC_Solution
set_option autoImplicit true
open TDLC
universe u

theorem TDLC.path2PreservesParity {A : Type u} {x y : A} {p q : Path x y}
    (cells : Path2 p q) : Path.parity p = Path.parity q := by sorry
