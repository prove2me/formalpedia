-- Prove2me | Theorems.Thm_RamseyGraphs_erdos_szekeres
-- name    : RamseyGraphs.erdos_szekeres
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:18:32.056065+00:00
-- url     : https://prove2.me/theorems/dcb6549d-ff5b-5af6-81af-db3b395e9304
-- title:
--   Ramsey Graphs: erdos szekeres
-- statement:
--   **Erdős–Szekeres (1935).** Every graph on at least `(s + t - 2).choose (s - 1)` vertices
--   contains `K_s` or an independent set of size `t`.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/Solution.lean#L40-L43
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/Solution.lean#L40-L43

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
public import Definitions.Def_RamseyGraphs_Solution
public import Theorems.Thm_RamseyLib_erdos_szekeres

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyGraphs

theorem RamseyGraphs.erdos_szekeres {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : ℕ) (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hV : (s + t - 2).choose (s - 1) ≤ Fintype.card V) :
    ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t := by sorry
