-- Prove2me | Theorems.Thm_SmoothedSimplex_TwoPhase_lemma_5_1_1
-- name    : SmoothedSimplex.TwoPhase.lemma_5_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:28:41.611327+00:00
-- url     : https://prove2.me/theorems/109c72fc-5861-4196-9d27-d83406d9fcef
-- title:
--   Lemma 5.1.1 (Many good choices)
-- statement:
--   Let $n>d\ge3$ and let $a_1,\ldots,a_n\in\mathbb R^d$ be independent Gaussian vectors of standard deviation $\sigma>0$, centered at points of norm at most one. With $X_I=[s_{\min}(A_I)\le\kappa_0]$, the probability that nearly every $d$-minor is bad satisfies
--   $$\Pr\!\left[\sum_{I\in\binom{[n]}d}X_I\ge\left(1-\frac1n\right)\binom nd\right]\le n^{-d}+n^{-n+d-1}+n^{-2.9d+1}.$$
--   The threshold $\kappa_0$ is equation (35). This result ensures the algorithm can sample a reasonably conditioned basis.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 5.1.1, printed p. 60, PDF p. 60

import Mathlib
import Definitions.Def_SmoothedSimplex_TwoPhase_kappaZero
import Definitions.Def_SmoothedSimplex_TwoPhase_shadowBoundD

namespace SmoothedSimplex.TwoPhase

/-- Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7,
Lemma 5.1.1 (Many good choices), printed p. 60, PDF p. 60. All vectors are independent isotropic Gaussians of standard deviation σ, with center norm at most one. Formalization Note: `[n]` is `Fin n`; probability measures use product Gaussian laws. -/
theorem lemma_5_1_1 {n d : ℕ} (hn : 3 ≤ d) (hnd : d < n)
    (c : Fin n → Point d) (hc : ∀ i, ‖c i‖ ≤ 1) (σ : ℝ) (hσ : 0 < σ) :
    ((gaussianFamily c σ) {a |
      ((∑ I ∈ Finset.univ.powersetCard d, badMinor a I σ) : ℝ) ≥
        (1 - 1 / (n : ℝ)) * Nat.choose n d}).toReal ≤
      (n : ℝ) ^ (-(d : ℝ)) + (n : ℝ) ^ (-(n : ℝ) + d - 1 : ℝ) +
        (n : ℝ) ^ (-(2.9 : ℝ) * d + 1) := by sorry

end SmoothedSimplex.TwoPhase
