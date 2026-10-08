-- Prove2me | Theorems.Thm_P7ThreeColor_Lemma11_display_1
-- name    : P7ThreeColor.Lemma11.display_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:18.067807+00:00
-- url     : https://prove2.me/theorems/f3087c2d-cd84-47ee-97e8-021714b1e98d
-- title:
--   Display (1), p. 6 — two non-adjacent vertices of N(S) are joined by an induced path through a seed S
-- statement:
--   Let $G$ be a finite graph with a palette $L$, and let $S$ be a seed of $(G,L)$: a nonempty 2-dominating set inducing a connected subgraph, with $|L(v)|=1$ on $S$ and $|L(v)|=2$ on $N(S)$.
--
--   Let $v, w \in N(S)$ be two distinct non-adjacent vertices. Then
--
--   $$\text{there is an induced } v\text{–}w \text{ path } P \text{ with at least } 3 \text{ vertices whose inner vertices all lie in } S.$$
--
--   This observation is used throughout Section 3.1, in particular to start the construction of the path in Claim 12.
--
--   **Formalization Note** An induced path is a nonempty list of distinct vertices in which two vertices are adjacent exactly when they are consecutive (`StrongPerfectGraph.Main.IsInducedPath`); its ends are the head and the last element of the list, and its inner vertices are the list with both ends removed.
-- source:
--   Bonomo, Chudnovsky, Maceli, Schaudt, Stein and Zhong, Three-coloring and list three-coloring of graphs without induced paths on seven vertices, Combinatorica (2017), DOI 10.1007/s00493-017-3553-8, p. 6, display (1)

import Mathlib
import Definitions.Def_P7ThreeColor_Lemma11_Seed
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath

namespace P7ThreeColor.Lemma11

open StrongPerfectGraph.Main in
/-- Display (1), p. 6: for a seed `S` and two distinct non-adjacent `v, w ∈ N(S)` there is an
induced `v`–`w` path on at least 3 vertices whose inner vertices all lie in `S`. -/
theorem display_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (L : V → Finset (Fin 3)) (S : Finset V) (hS : IsSeed G L S)
    (v w : V) (hv : v ∈ P7ThreeColor.Seed.nbhd G S) (hw : w ∈ P7ThreeColor.Seed.nbhd G S) (hvw : v ≠ w) (hnadj : ¬ G.Adj v w) :
    ∃ p : List V, IsInducedPath G p ∧ p.head? = some v ∧ p.getLast? = some w ∧
      3 ≤ p.length ∧ ∀ z ∈ p.tail.dropLast, z ∈ S := by sorry

end P7ThreeColor.Lemma11
