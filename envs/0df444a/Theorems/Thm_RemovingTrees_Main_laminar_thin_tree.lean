-- Prove2me | Theorems.Thm_RemovingTrees_Main_laminar_thin_tree
-- name    : RemovingTrees.Main.laminar_thin_tree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T15:21:18.372791+00:00
-- url     : https://prove2.me/theorems/f5db0a6a-4ed5-433a-a2e2-b2fb62af9d36
-- title:
--   Theorem 3.2 — Constructive 22-thin tree for a laminar family
-- statement:
--   Let $G$ be a connected finite undirected multigraph on at least two vertices, let $F$ be its active edge set, let $x\in P_{\rm ST}(F)$ be any real point of the convex hull of spanning-tree incidence vectors, and let $\mathcal L$ be any laminar family of shores. A single uniform polynomial-time procedure returns a spanning tree $T\subseteq F$ satisfying
--   $$
--   |\delta_T(S)|\le22\sum_{e\in\delta_F(S)}x_e\qquad(S\in\mathcal L).
--   $$
--   Its exact-arithmetic implementation accepts all real $x$, including boundary points and zero coordinates. A bit implementation accepts rational coordinates with running time polynomial in their full binary encoding and in the explicitly listed family and graph.
--
--   The result is the source's cited laminar thin-tree rounding tool. The returned edges belong to the active graph; the theorem assumes no thinness or rounding oracle.
--
--   **Formalization Note** A finite list represents the input family by its set of entries. The exact-real program receives $m$ supplied real coordinates; the bit program receives signed rational encodings. The two programs share a uniform polynomial upper bound.
--
--   Differences from the source:
--   - encoding: finite undirected multigraphs on at least two vertices → vertices Fin n with n ≥ 2 and individually labeled edges Fin m with symmetric endpoint cuts; reason: every source graph admits such labels; loops and parallel edges are retained
--   - encoding: efficient construction with real-valued data → charged finite exact-arithmetic/sign machine for all real inputs, with a separate bit implementation for rational inputs where stated; reason: retains every real input and measures bit cost on the rational data used by the paper
--   - encoding: a graph G → an ambient labeled graph with an explicit active edge subset F; reason: taking F to be all edges recovers the source; relabeling F gives the same graph and allows subgraph calls
-- source:
--   Nathan Klein, Neil Olver, Zi Song Yeoh, STOC 2027 submission #1092 (October 2026), Theorem 3.2 [KO23], p.4

import Mathlib
import Definitions.Def_RemovingTrees_Main_GraphModel

set_option autoImplicit false

namespace RemovingTrees.Main

/-- Theorem 3.2 [KO23], p.4. The exact-real and rational bit implementations
have the same mathematical output requirement, including the constant 22. -/
theorem laminar_thin_tree :
    ∃ R : RealMachine, ∃ B : OAI.CurrentKS.Machine, ∃ a d : ℕ, 0 < a ∧
    (∀ (n m : ℕ) (G : MultiGraph n m) (F : Finset (Fin m))
      (L : List (Finset (Fin n))) (x : Fin m → ℝ),
      2 ≤ n → Connected G F → x ∈ spanningTreePolytope G F →
      SteinerCutDominants.IsLaminar L.toFinset →
      RealResult R a d (encGraph G ++ encSet F ++ encList encSet L) (List.ofFn x)
        (TreeOutput G (fun T => ThinOn G F T x L.toFinset))) ∧
    (∀ (n m : ℕ) (G : MultiGraph n m) (F : Finset (Fin m))
      (L : List (Finset (Fin n))) (x : Fin m → ℚ),
      2 ≤ n → Connected G F →
      (fun e => (x e : ℝ)) ∈ spanningTreePolytope G F →
      SteinerCutDominants.IsLaminar L.toFinset →
      BitResult B a d
        (encGraph G ++ encSet F ++ encList encSet L ++ encList encRat (List.ofFn x))
        (TreeOutput G (fun T => ThinOn G F T (fun e => (x e : ℝ)) L.toFinset))) := by sorry
end RemovingTrees.Main
