-- Prove2me | Theorems.Thm_RamseyLib_es_finset
-- name    : RamseyLib.es_finset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:15:38.943068+00:00
-- url     : https://prove2.me/theorems/c6d7e6be-3a60-548e-9a6b-e695c6cf8048
-- title:
--   Ramsey Lib: es finset
-- statement:
--   Finset version of Erdős–Szekeres: every Finset `S` with `(s + t).choose s ≤ |S|` contains an
--   `(s + 1)`-clique of `G` or a `(t + 1)`-clique of `Gᶜ`.
--
--   Source: https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L31-L79
-- source:
--   https://github.com/jtraverso/ramsey-graph-bounds/blob/562986a7ce9edf086c20b3a2b8c7d5ace2ffd843/RamseyLib/Bounds.lean#L31-L79

module
public import Mathlib
public import Definitions.Def_RamseyLib_Bounds
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open RamseyLib

theorem RamseyLib.es_finset {V : Type*} (G : SimpleGraph V) :
    ∀ (s t : ℕ) (S : Finset V), (s + t).choose s ≤ S.card →
      (∃ T ⊆ S, G.IsNClique (s + 1) T) ∨ (∃ T ⊆ S, Gᶜ.IsNClique (t + 1) T) := by sorry
