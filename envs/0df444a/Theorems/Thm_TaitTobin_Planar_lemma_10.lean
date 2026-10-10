-- Prove2me | Theorems.Thm_TaitTobin_Planar_lemma_10
-- name    : TaitTobin.Planar.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T11:47:39.344363+00:00
-- url     : https://prove2.me/theorems/846fc5db-f774-4c07-b172-332c5bf6b080
-- title:
--   Lemma 10, p. 9 — every eigenvector entry exceeds 1/√(6n)
-- statement:
--   For all sufficiently large $n$: let $G$ be a planar graph on $n$ vertices of maximum spectral radius among planar graphs on $n$ vertices, $\mathbf v$ a positive eigenvector for $\lambda_1(G)$ with maximum entry $1$, and $x$ a vertex with $\mathbf v_x = 1$. Then every vertex $z$ satisfies
--   $$\mathbf v_z > \frac{1}{\sqrt{6n}}.$$
--
--   This lower bound converts upper bounds on sums of eigenvector entries into upper bounds on numbers of vertices.
--
--   **Formalization Note** Positivity of $\mathbf v$ is a hypothesis; it holds for the Perron vector of the (connected) maximizer.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 9, Lemma 10

import Mathlib
import Definitions.Def_TaitTobin_Planar_Setting

namespace TaitTobin.Planar

open Classical WangKangXue.SpectralTuran RobertsonSeymour1986.GM5

/-- Lemma 10, p. 9: for all large `n`, in a planar graph of maximum spectral radius with Perron
vector `v` (maximum entry `1`), every vertex `z` has `v_z > 1/√(6n)`. -/
theorem lemma_10 : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    TaitTobin.Outerplanar.IsSpecMax IsPlanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        ∀ z : Fin n, 1 / Real.sqrt (6 * (n : ℝ)) < v z := by sorry
end TaitTobin.Planar
