-- Prove2me | Theorems.Thm_RamseyLib_erdos_szekeres
-- name    : RamseyLib.erdos_szekeres
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:15:40.761091+00:00
-- url     : https://prove2.me/theorems/e6707e42-8919-5f3a-8345-12daa6f08de0
-- title:
--   Ramsey Lib: erdos szekeres
-- statement:
--   **Erdős–Szekeres (1935).** Every graph on at least `(s + t - 2).choose (s - 1)` vertices
--   contains `K_s` or an independent set of size `t`.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L101-L111
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L101-L111

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib

theorem RamseyLib.erdos_szekeres {V : Type*} [Fintype V] (G : SimpleGraph V) (s t : ℕ) (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hV : (s + t - 2).choose (s - 1) ≤ Fintype.card V) :
    ¬ G.CliqueFree s ∨ ¬ Gᶜ.CliqueFree t := by sorry
