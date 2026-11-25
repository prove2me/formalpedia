-- Prove2me | Theorems.Thm_PerfectGraph_isPerfect_iff_card_le
-- name    : PerfectGraph.isPerfect_iff_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:30:14.345236+00:00
-- url     : https://prove2.me/theorems/fa1ba191-af19-59d0-b3e8-615c6bd3ba6d
-- title:
--   Perfect Graph: is Perfect iff card le
-- statement:
--   **Lovász (1972).** A finite graph is perfect if and only if `|S| ≤ α(G[S]) ω(G[S])` for every
--   vertex set `S`.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Perfect.lean#L37-L58
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Perfect.lean#L37-L58

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
public import Definitions.Def_PerfectLib_Perfect
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PerfectGraph
variable {V : Type*}

theorem PerfectGraph.isPerfect_iff_card_le [Finite V] (G : SimpleGraph V) :
    IsPerfect G ↔ ∀ S : Finset V,
      S.card ≤ (G.induce (S : Set V)).indepNum * (G.induce (S : Set V)).cliqueNum := by sorry
