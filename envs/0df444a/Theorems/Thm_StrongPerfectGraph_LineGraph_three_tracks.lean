-- Prove2me | Theorems.Thm_StrongPerfectGraph_LineGraph_three_tracks
-- name    : StrongPerfectGraph.LineGraph.three_tracks
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T02:47:50.112853+00:00
-- url     : https://prove2.me/theorems/6646a4c2-f1f5-43a9-99be-e2c3564bfaf7
-- title:
--   7.1, p. 92 — three internally disjoint tracks through prescribed edges in a 3-connected graph
-- statement:
--   Let $c_1, c_2$ be adjacent vertices of a $3$-connected graph $J$, and let $e = c_1x$ and $f = c_1y$ be two distinct edges of $J$ incident with $c_1$ and different from $c_1c_2$. Then there are three tracks of $J$ from $c_1$ to $c_2$, pairwise vertex-disjoint except for their ends, whose first edges are $c_1c_2$, $e$ and $f$ respectively.
--
--   The lemma is used to build prisms around a branch of an appearance in the rung-replacement argument of §7.
--
--   **Formalization Note** The track with first edge $c_1c_2$ is the edge $c_1c_2$ itself; the other two are $c_1, x, \dots, c_2$ and $c_1, y, \dots, c_2$ with disjoint interiors. The page writes "edges $e, f$"; they are taken distinct, as the conclusion (three tracks pairwise disjoint except for their ends) requires.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 92, 7.1

import Mathlib
import Definitions.Def_StrongPerfectGraph_LineGraph_IsSubdivision

namespace StrongPerfectGraph.LineGraph

theorem three_tracks {W : Type*} [Fintype W] (J : SimpleGraph W) (hJ : IsThreeConnected J)
    (c₁ c₂ x y : W) (h₁₂ : J.Adj c₁ c₂) (hx : J.Adj c₁ x) (hy : J.Adj c₁ y)
    (hx₂ : x ≠ c₂) (hy₂ : y ≠ c₂) (hxy : x ≠ y) :
    IsTrack J [c₁, c₂] ∧
      ∃ q r : List W, IsTrack J (c₁ :: x :: q ++ [c₂]) ∧ IsTrack J (c₁ :: y :: r ++ [c₂]) ∧
        ∀ z ∈ x :: q, z ∉ y :: r := by sorry

end StrongPerfectGraph.LineGraph
