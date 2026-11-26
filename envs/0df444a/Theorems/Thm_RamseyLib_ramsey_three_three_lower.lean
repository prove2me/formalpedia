-- Prove2me | Theorems.Thm_RamseyLib_ramsey_three_three_lower
-- name    : RamseyLib.ramsey_three_three_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:15:47.297221+00:00
-- url     : https://prove2.me/theorems/2c41d6aa-582d-407e-81b1-bccb4402fa33
-- title:
--   Ramsey Lib: ramsey three three lower
-- statement:
--   **`R(3, 3) > 5`.** The pentagon has neither a triangle nor an independent set of size
--   three.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L93-L97
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L93-L97

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib

theorem RamseyLib.ramsey_three_three_lower :
    ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3 := by sorry
