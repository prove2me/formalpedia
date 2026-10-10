-- Prove2me | Theorems.Thm_TaitTobin_Planar_lemma_12
-- name    : TaitTobin.Planar.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:47:33.801063+00:00
-- url     : https://prove2.me/theorems/c7318f26-d7f5-42f4-9f53-70420b7cd9a9
-- title:
--   Lemma 12, p. 11 — every vertex other than x and w has eigenvector entry below 1/10
-- statement:
--   There is $\varepsilon_0 > 0$ such that for every $0 < \varepsilon < \varepsilon_0$ and all sufficiently large $n$ the following holds. Let $G$ be a planar graph on $n$ vertices of maximum spectral radius among planar graphs on $n$ vertices, $\mathbf v$ a positive eigenvector for $\lambda_1(G)$ with maximum entry $1$, and $x$ a vertex with $\mathbf v_x = 1$. Let $w$ be any vertex as in Lemma 11: $w \in L$, $w \ne x$, $\mathbf v_w > 1 - 24\varepsilon$ and $|\{y \in S : y \not\sim w\}| \le 94\varepsilon n$. Then
--   $$\mathbf v_u < \frac{1}{10} \qquad\text{for every vertex } u \notin \{x, w\}.$$
--
--   So outside the two hubs all eigenvector entries are small, which is what makes the edge switches of Lemmas 13 and 14 increase $\lambda_1$.
--
--   **Formalization Note** The paper names the vertex $v$, the same letter as the eigenvector; it is renamed $u$. The lemma is stated for every $w$ satisfying the conclusion of Lemma 11, which is how the paper uses "the vertex from Lemma 11".
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 11, Lemma 12

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- Lemma 12, p. 11: for every sufficiently small `ε > 0` and all large `n`, in a planar graph of
maximum spectral radius, if `w` is a vertex as in Lemma 11 then every vertex `u ∉ {x, w}` has
`v_u < 1/10` (the paper calls this vertex `v`). -/
theorem lemma_12 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∀ w : Fin n, IsSecondHub G ε v x w →
          ∀ u : Fin n, u ≠ x → u ≠ w → v u < 1 / 10 := by sorry
end TaitTobin.Planar
