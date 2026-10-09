-- Prove2me | Theorems.Thm_TaitTobin_Irregularity_eq_11
-- name    : TaitTobin.Irregularity.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:07.19812+00:00
-- url     : https://prove2.me/theorems/34f5b121-8ea9-4630-b134-cbdff0385208
-- title:
--   Eq. (11), p. 17 — n/2 + √n + 5 ≥ vᵗv > n/2 − 2εn − O(√n)
-- statement:
--   For every $\varepsilon > 0$ there are constants $K$ and $N$ such that for every $n \ge N$ the following holds. Let $G$ be a connected graph on $n$ vertices maximizing $\lambda_1 - d$, and let $\mathbf v$ be a leading eigenvector of its adjacency matrix with positive entries and maximum entry $1$. Then
--   $$\frac n2 + \sqrt n + 5 \;\ge\; \mathbf v^{t}\mathbf v \;>\; \frac n2 - 2\varepsilon n - K\sqrt n .$$
--
--   The squared norm of the normalized Perron vector is thus $n/2 + O(\varepsilon n + \sqrt n)$. It is the denominator of every Rayleigh-quotient comparison in Section 4, in particular in Lemma 19.
--
--   **Formalization Note** $\mathbf v^t\mathbf v = \sum_i \mathbf v_i^2$. The paper's $O(\sqrt n)$ is $K\sqrt n$ with $K$ depending only on $\varepsilon$. The hypothesis that some entry equals $1$ is the normalization; the upper bound does not depend on $\varepsilon$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 17, eq. (11) (proof of Lemma 19)

import Mathlib
import Definitions.Def_TaitTobin_Irregularity_Setting

namespace TaitTobin.Irregularity

open Classical WangKangXue.SpectralTuran

/-- Inequality (11), p. 17 (proof of Lemma 19): for every `ε > 0` there is `K` such that for `n`
large, the Perron vector `v` (maximum entry `1`) of a maximizer of `λ₁ − d` satisfies
`n/2 + √n + 5 ≥ vᵗv > n/2 − 2εn − K√n`. -/
theorem eq_11 : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
    IsIrregMax G →
    ∀ v : Fin n → ℝ, (G.adjMatrix ℝ).mulVec v = specRad G • v →
      (∀ i, 0 < v i) → (∀ i, v i ≤ 1) → (∃ x : Fin n, v x = 1) →
      ∑ i, v i ^ 2 ≤ (n : ℝ) / 2 + Real.sqrt n + 5 ∧
      (n : ℝ) / 2 - 2 * ε * n - K * Real.sqrt n < ∑ i, v i ^ 2 := by sorry
end TaitTobin.Irregularity
