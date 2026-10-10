-- Prove2me | Theorems.Thm_TaitTobin_Planar_lemma_13
-- name    : TaitTobin.Planar.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:48:07.627981+00:00
-- url     : https://prove2.me/theorems/9035ab9d-be77-4cea-8eb1-83009a224b15
-- title:
--   Lemma 13, p. 11 — in the extremal graph the two hubs are adjacent: x ∼ w
-- statement:
--   There is $\varepsilon_0 > 0$ such that for every $0 < \varepsilon < \varepsilon_0$ and all sufficiently large $n$ the following holds. Let $G$ be a planar graph on $n$ vertices of maximum spectral radius among planar graphs on $n$ vertices (an *extremal* graph), $\mathbf v$ a positive eigenvector for $\lambda_1(G)$ with maximum entry $1$, $x$ a vertex with $\mathbf v_x = 1$, and $w$ any vertex as in Lemma 11. Then
--   $$x \sim w.$$
--
--   Adjacency of the hubs is what allows a vertex to be attached to both of them while keeping the graph planar, which is used in Lemma 14.
--
--   **Formalization Note** The lemma is stated for every $w$ satisfying the conclusion of Lemma 11.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 11, Lemma 13 (proof on p. 12)

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- Lemma 13, p. 11: for every sufficiently small `ε > 0` and all large `n`, in a planar graph of
maximum spectral radius, if `w` is a vertex as in Lemma 11 then `x ∼ w`. -/
theorem lemma_13 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∀ w : Fin n, IsSecondHub G ε v x w → G.Adj x w := by sorry
end TaitTobin.Planar
