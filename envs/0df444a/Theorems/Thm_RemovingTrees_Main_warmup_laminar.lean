-- Prove2me | Theorems.Thm_RemovingTrees_Main_warmup_laminar
-- name    : RemovingTrees.Main.warmup_laminar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-09T15:21:34.556503+00:00
-- url     : https://prove2.me/theorems/4883cb2b-dcc0-4a08-bda5-d315bc408f3b
-- title:
--   Lemma 3.5 — The warm-up deficient family is laminar
-- statement:
--   Let $G$ be a finite undirected multigraph on at least two vertices, with every nontrivial cut containing at least a positive even integer $k$ edges. Fix a list of $k/2$ edge-disjoint spanning trees, a positive integer $C$ with $44C\le k/2$, and a root vertex $r$. Reserve the first $44C$ trees, let $H$ be their union, and put $R=G-H$. Then
--   $$
--   \mathcal N=\{S\subseteq V\setminus\{r\}: |\delta_R(S)|<3k/4-66C\}
--   $$
--   is a laminar family: any two members are disjoint or one contains the other.
--
--   This supplies the specific family to which laminar thin-tree rounding applies in the warm-up construction. It asserts no laminarity for an arbitrary family supplied without this reserved-packing preamble.
--
--   Differences from the source:
--   - encoding: finite undirected multigraphs on at least two vertices → vertices Fin n with n ≥ 2 and individually labeled edges Fin m with symmetric endpoint cuts; reason: every source graph admits such labels; loops and parallel edges are retained
--   - encoding: H is the union of 44C trees of a k/2-tree packing → H is the union of the first 44C trees of an ordered packing and 44C ≤ k/2; reason: ordering can put any selected group first; the bound is necessary for the source reservation to exist
--   - generalization: the warm-up starts with k = λ(G) → any positive even connectivity lower bound k with the stated packing; reason: the argument uses only this packing and lower bound; equality recovers every source instance
-- source:
--   Nathan Klein, Neil Olver, Zi Song Yeoh, STOC 2027 submission #1092 (October 2026), Lemma 3.5 and Eq.(1), p.5

import Mathlib
import Definitions.Def_RemovingTrees_Main_GraphModel

set_option autoImplicit false

namespace RemovingTrees.Main

/-- Lemma 3.5, p.5, with the complete Eq.(1) reserved-packing preamble. -/
theorem warmup_laminar {n m : ℕ} (G : MultiGraph n m) (hn : 2 ≤ n)
    (k C : ℕ) (hk : 0 < k) (hC : 0 < C) (heven : Even k) (hG : CutLower G Finset.univ k)
    (ts : List (Finset (Fin m))) (hpack : Packing G Finset.univ ts)
    (hlen : ts.length = k / 2) (hreserve : 44*C ≤ k / 2) (root : Fin n) :
    SteinerCutDominants.IsLaminar
      (rootedLowCuts G (Finset.univ \ treeUnion (ts.take (44*C))) root
        ((3:ℝ)/4*k - 66*C)) := by sorry
end RemovingTrees.Main
