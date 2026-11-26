-- Prove2me | Theorems.Thm_RamseyLib_erdos_lower_bound
-- name    : RamseyLib.erdos_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:15:54.994904+00:00
-- url     : https://prove2.me/theorems/d567de64-045e-4f9d-852f-f56e2d7bb839
-- title:
--   Ramsey Lib: erdos lower bound
-- statement:
--   **Erdős (1947).** For `k ≥ 3` and `n ≤ 2 ^ (k / 2)` there is a graph on `n` vertices with
--   neither `K_k` nor an independent set of size `k`.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L165-L258
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L165-L258

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib

theorem RamseyLib.erdos_lower_bound (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (hn : (n : ℝ) ≤ 2 ^ ((k : ℝ) / 2)) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by sorry
