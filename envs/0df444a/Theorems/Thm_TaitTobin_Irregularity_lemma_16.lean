-- Prove2me | Theorems.Thm_TaitTobin_Irregularity_lemma_16
-- name    : TaitTobin.Irregularity.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:09:22.101974+00:00
-- url     : https://prove2.me/theorems/65b7cbb2-62b7-404f-a117-da787c1fdb68
-- title:
--   Lemma 16, p. 14 — a maximizer of λ₁ − d has λ₁ = n/2 + c₁√n and d = n/4 + c₂√n with |c₁|, |c₂| < 1
-- statement:
--   There is $N$ such that for every $n \ge N$ the following holds. Let $G$ be a connected graph on $n$ vertices that maximizes $\lambda_1 - d$ among all connected graphs on $n$ vertices, where $\lambda_1$ is the spectral radius and $d = 2e(G)/n$ the average degree. Then
--   $$\left|\lambda_1(G) - \frac n2\right| < \sqrt n \qquad\text{and}\qquad \left|\frac{2e(G)}{n} - \frac n4\right| < \sqrt n .$$
--
--   Equivalently, $\lambda_1(G) = n/2 + c_1\sqrt n$ and $2e(G)/n = n/4 + c_2\sqrt n$ with $|c_1|, |c_2| < 1$. This is the first structural fact about the extremal graph: about half of the vertices must carry most of the spectral weight, and the graph has about $n^2/8$ edges.
--
--   **Formalization Note** "For $n$ large enough", which the proof states at its end, is the threshold $N$. The page's constants $c_1, c_2$ are eliminated by writing $c_i = (\cdot - \cdot)/\sqrt n$.
-- source:
--   Tait and Tobin, Three conjectures in extremal spectral graph theory, arXiv:1606.01916v2, p. 14, Lemma 16

import Mathlib
import Definitions.Def_TaitTobin_Irregularity_Setting

namespace TaitTobin.Irregularity

open Classical WangKangXue.SpectralTuran

/-- Lemma 16, p. 14: for `n` large, a connected graph `G` on `n` vertices maximizing `λ₁ − d` has
`λ₁ = n/2 + c₁√n` and `2e(G)/n = n/4 + c₂√n` with `|c₁|, |c₂| < 1`. -/
theorem lemma_16 : ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), IsIrregMax G →
    |specRad G - (n : ℝ) / 2| < Real.sqrt n ∧ |avgDeg G - (n : ℝ) / 4| < Real.sqrt n := by sorry
end TaitTobin.Irregularity
