-- Prove2me | Theorems.Thm_TaitTobin_Outerplanar_lemma_5
-- name    : TaitTobin.Outerplanar.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:29.81098+00:00
-- url     : https://prove2.me/theorems/1841e092-2e6d-49d7-84a7-3a2fe4f2b0ea
-- title:
--   Lemma 5, p. 6 — d_x > n − 11√n, and v_u < C₁/√n for every u ≠ x, for n large
-- statement:
--   There are an absolute constant $C_1$ and a threshold $N$ such that the following holds for every $n \ge N$. Let $G$ be an outerplanar graph on $n$ vertices of maximum spectral radius $\lambda_1$ among outerplanar graphs on the same $n$ vertices, let $\mathbf v$ be a positive eigenvector for $\lambda_1$ normalized so that its maximum entry is $1$, and let $x$ be a vertex with $\mathbf v_x = 1$. Then
--   $$d_x > n - 11\sqrt n \qquad\text{and}\qquad \mathbf v_u < \frac{C_1}{\sqrt n}\quad\text{for every vertex } u \ne x.$$
--
--   So the maximizer has a single vertex of large degree, and all other eigenvector entries are of order $n^{-1/2}$.
--
--   **Formalization Note** The constant $C_1$ is quantified before $N$, $n$, $G$, $\mathbf v$ and $x$, so it does not depend on the graph; the paper's proof gives $C_1 = 23$. The statement holds for every admissible $\mathbf v$ and every vertex $x$ with $\mathbf v_x = 1$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 6, Lemma 5

import Mathlib
import Definitions.Def_TaitTobin_Outerplanar_Setting

namespace TaitTobin.Outerplanar

open Classical WangKangXue.SpectralTuran

/-- Lemma 5, p. 6: there are an absolute constant `C₁` and a threshold `N` such that, for
`n ≥ N`, in an outerplanar graph on `n` vertices of maximum spectral radius, with Perron vector `v`
normalized to maximum entry `1` and `v x = 1`, we have `d_x > n - 11√n` and `v_u < C₁/√n` for every
`u ≠ x`. -/
theorem lemma_5 : ∃ C₁ : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    IsSpecMax IsOuterplanar G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
        (n : ℝ) - 11 * Real.sqrt n < (G.degree x : ℝ) ∧
          ∀ u : Fin n, u ≠ x → v u < C₁ / Real.sqrt n := by sorry
end TaitTobin.Outerplanar
