-- Prove2me | Theorems.Thm_PerfectGraphTheorem_isPerfect_iff_card_le
-- name    : PerfectGraphTheorem.isPerfect_iff_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:56:16.350883+00:00
-- url     : https://prove2.me/theorems/be703682-17f3-4114-b9aa-9b256d847d4a
-- title:
--   Perfect Graph Theorem: is Perfect iff card le
-- statement:
--   **Lovász (1972).** A finite graph is perfect if and only if `|S| ≤ α(G[S]) ω(G[S])` for every
--   vertex set `S`.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/Solution.lean#L37-L40
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/Solution.lean#L37-L40

module
public import Mathlib
public import Definitions.Def_PerfectLib_Perfect
public import Definitions.Def_PerfectGraphs_Solution
public import Theorems.Thm_PerfectGraph_isPerfect_iff_card_le

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PerfectGraphTheorem
variable {V : Type*}

theorem PerfectGraphTheorem.isPerfect_iff_card_le [Finite V] (G : SimpleGraph V) :
    IsPerfect G ↔ ∀ S : Finset V,
      S.card ≤ (G.induce (S : Set V)).indepNum * (G.induce (S : Set V)).cliqueNum := by sorry
