-- Prove2me | Theorems.Thm_PerfectGraph_gasparian
-- name    : PerfectGraph.gasparian
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T10:30:44.757673+00:00
-- url     : https://prove2.me/theorems/1acc5e6d-d328-5c6a-89be-57a7eafed41e
-- title:
--   Perfect Graph: gasparian
-- statement:
--   **Gasparian's lemma.** If `G[S]` is not `ω(G[S])`-colourable but every proper subset `T` of
--   `S` has `G[T]` `ω(G[T])`-colourable, then `|S| ≥ α(G[S]) ω(G[S]) + 1`.
--
--   Source: https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L127-L302
-- source:
--   https://github.com/jtraverso/perfect-graphs/blob/796922460172c4e51c39c96575d03957652c0bab/PerfectLib/Gasparian.lean#L127-L302

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open PerfectGraph
variable {V : Type*} (G : SimpleGraph V)

theorem PerfectGraph.gasparian [Finite V] {S : Finset V}
    (hnot : ¬ IsColOn G S (G.induce (S : Set V)).cliqueNum)
    (hmin : ∀ T ⊂ S, IsColOn G T (G.induce (T : Set V)).cliqueNum) :
    (G.induce (S : Set V)).indepNum * (G.induce (S : Set V)).cliqueNum + 1 ≤ S.card := by sorry
