-- Prove2me | Theorems.Thm_RamseyLib_ramsey_three_three_upper
-- name    : RamseyLib.ramsey_three_three_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:15:45.432907+00:00
-- url     : https://prove2.me/theorems/6f145ec8-2a90-44a0-a1da-fa4f5c1fdff3
-- title:
--   Ramsey Lib: ramsey three three upper
-- statement:
--   **`R(3, 3) ≤ 6`.** Every graph on six vertices contains a triangle or an independent set of
--   size three.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L84-L89
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L84-L89

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib

theorem RamseyLib.ramsey_three_three_upper (G : SimpleGraph (Fin 6)) :
    ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 3 := by sorry
