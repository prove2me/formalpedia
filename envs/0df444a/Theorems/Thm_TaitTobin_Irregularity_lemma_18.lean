-- Prove2me | Theorems.Thm_TaitTobin_Irregularity_lemma_18
-- name    : TaitTobin.Irregularity.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:03.485992+00:00
-- url     : https://prove2.me/theorems/8e5f3e13-c890-48d0-a156-f4cafcf02d92
-- title:
--   Lemma 18, p. 15 — a vertex u ≠ x with v_u > 1 − 2ε, d_u − λ₁v_u = O(√n) and d_u ≥ (1/2 − 2ε)n
-- statement:
--   For every $\varepsilon > 0$ there are constants $K$ and $N$ such that for every $n \ge N$ the following holds. Let $G$ be a connected graph on $n$ vertices maximizing $\lambda_1 - d$, let $\mathbf v$ be a leading eigenvector with positive entries and maximum entry $1$, and let $x$ be a vertex with $\mathbf v_x = 1$. Then there is a vertex $u \ne x$ with
--   $$\mathbf v_u > 1 - 2\varepsilon, \qquad d_u - \lambda_1 \mathbf v_u \le K\sqrt n, \qquad d_u \ge \Bigl(\frac12 - 2\varepsilon\Bigr) n .$$
--
--   A second vertex of nearly maximal eigenvector entry and degree about $n/2$ is the seed of the clique $U$ of Proposition 20.
--
--   **Formalization Note** The paper's $d_u - \lambda_1\mathbf v_u = O(\sqrt n)$ is the bound $\le K\sqrt n$ with $K$ depending only on $\varepsilon$ (the proof's "$K$ large enough depending only on $\epsilon$"); the lower bound $d_u - \lambda_1\mathbf v_u \ge 0$ holds for every vertex and is not repeated. The proof works for every fixed $\varepsilon > 0$, so $\varepsilon$ is universally quantified and $N$ depends on it. The eigenvector conventions are those of Lemma 17.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 15, Lemma 18

import Mathlib
import Definitions.Def_TaitTobin_Irregularity_Setting

namespace TaitTobin.Irregularity

open Classical WangKangXue.SpectralTuran

/-- Lemma 18, p. 15: for every `ε > 0` there is `K` (depending only on `ε`) such that for `n`
large, every maximizer `G` of `λ₁ − d` with Perron vector `v` (maximum entry `v_x = 1`) has a vertex
`u ≠ x` with `v_u > 1 − 2ε`, `d_u − λ₁ v_u ≤ K √n` and `d_u ≥ (1/2 − 2ε) n`. -/
theorem lemma_18 : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    IsIrregMax G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → ∀ x : Fin n, v x = 1 →
      ∃ u : Fin n, u ≠ x ∧ 1 - 2 * ε < v u ∧
        (G.degree u : ℝ) - specRad G * v u ≤ K * Real.sqrt n ∧
        (1 / 2 - 2 * ε) * (n : ℝ) ≤ (G.degree u : ℝ) := by sorry
end TaitTobin.Irregularity
