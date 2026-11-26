-- Prove2me | Theorems.Thm_RamseyGraphs_erdos_lower_bound
-- name    : RamseyGraphs.erdos_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:20:24.303286+00:00
-- url     : https://prove2.me/theorems/256ea6c0-7102-59f2-a25e-edea456e1c0f
-- title:
--   Ramsey Graphs: erdos lower bound
-- statement:
--   **Erdős (1947).** For `k ≥ 3` and `n ≤ 2 ^ (k / 2)` there is a graph on `n` vertices with
--   neither `K_k` nor an independent set of size `k`.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/Solution.lean#L47-L49
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/Solution.lean#L47-L49

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
public import Definitions.Def_RamseyGraphs_Solution
public import Theorems.Thm_RamseyLib_erdos_lower_bound

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyGraphs

theorem RamseyGraphs.erdos_lower_bound (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : (n : ℝ) ≤ 2 ^ ((k : ℝ) / 2)) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by sorry
