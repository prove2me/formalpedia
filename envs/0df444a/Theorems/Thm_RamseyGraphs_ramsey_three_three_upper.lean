-- Prove2me | Theorems.Thm_RamseyGraphs_ramsey_three_three_upper
-- name    : RamseyGraphs.ramsey_three_three_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:34.230014+00:00
-- url     : https://prove2.me/theorems/cfb6ef99-074e-55ff-b7db-baf2c2ba57e2
-- title:
--   Ramsey Graphs: ramsey three three upper
-- statement:
--   **`R(3, 3) ≤ 6`.** Every graph on six vertices contains a triangle or an independent set of
--   size three.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/Solution.lean#L28-L30
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/Solution.lean#L28-L30

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
public import Definitions.Def_RamseyGraphs_Solution
public import Theorems.Thm_RamseyLib_ramsey_three_three_upper

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyGraphs

theorem RamseyGraphs.ramsey_three_three_upper (G : SimpleGraph (Fin 6)) :
    ¬ G.CliqueFree 3 ∨ ¬ Gᶜ.CliqueFree 3 := by sorry
