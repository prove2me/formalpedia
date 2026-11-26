-- Prove2me | Theorems.Thm_RamseyGraphs_ramsey_three_three_lower
-- name    : RamseyGraphs.ramsey_three_three_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:17:51.745389+00:00
-- url     : https://prove2.me/theorems/bfc9233d-dc69-4296-93e7-a3378f5af10b
-- title:
--   Ramsey Graphs: ramsey three three lower
-- statement:
--   **`R(3, 3) > 5`.** The pentagon has neither a triangle nor an independent set of size
--   three.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/Solution.lean#L34-L36
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/Solution.lean#L34-L36

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
public import Definitions.Def_RamseyGraphs_Solution
public import Theorems.Thm_RamseyLib_ramsey_three_three_lower

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyGraphs

theorem RamseyGraphs.ramsey_three_three_lower :
    ∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3 := by sorry
