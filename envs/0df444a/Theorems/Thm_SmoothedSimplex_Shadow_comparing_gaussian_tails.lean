-- Prove2me | Theorems.Thm_SmoothedSimplex_Shadow_comparing_gaussian_tails
-- name    : SmoothedSimplex.Shadow.comparing_gaussian_tails
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T12:47:50.320235+00:00
-- url     : https://prove2.me/theorems/c587c5be-4961-4577-8242-9fb1e15159ca
-- title:
--   Lemma 2.4.11 — comparing Gaussian tails
-- statement:
--   Let $0<\sigma\le1$ and let $\mu(t)=\frac{1}{\sqrt{2\pi}\,\sigma}e^{-t^2/2\sigma^2}$ be the density of the centered normal distribution with variance $\sigma^2$. Then for $x\le 2$ and $|x-y|\le\varepsilon$,
--
--   $$
--   \frac{\int_{t=y}^{\infty}\mu(t)\,dt}{\int_{t=x}^{\infty}\mu(t)\,dt}\ \ge\ 1-\frac{8\varepsilon}{3\sigma^{2}}. \tag{6}
--   $$
--
--   Moving the threshold of a Gaussian tail by $\varepsilon$ changes its mass by a relative factor of order $\varepsilon/\sigma^2$, as long as the threshold is not far out in the tail; Lemma 4.2.3 applies this to halfspace probabilities.
--
--   **Formalization Note** The tail integrals are the masses of $[x,\infty)$ and $[y,\infty)$ under `gaussianReal 0 σ²`; the ratio is cross-multiplied (the denominator is positive).
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, Lemma 2.4.11, eq. (6), printed p. 23 (PDF p. 23)

import Mathlib

namespace SmoothedSimplex.Shadow

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- **Lemma 2.4.11 (Comparing Gaussian tails)** (Spielman & Teng, arXiv:cs/0111050v7,
Lemma 2.4.11, printed p. 23, PDF p. 23). Let `σ ≤ 1` and let `µ(t) = (1/(√(2π)σ)) e^{−t²/2σ²}`.
Then, for `x ≤ 2` and `|x − y| ≤ ε`,
`∫_{t=y}^∞ µ(t) dt / ∫_{t=x}^∞ µ(t) dt ≥ 1 − 8ε/(3σ²)`.

**Formalization Note.** `σ > 0`. `µ` is the density of `gaussianReal 0 σ²`, so
`∫_{t=y}^∞ µ(t) dt = gaussianReal 0 σ² [y, ∞)`. The ratio is cross-multiplied (the denominator is
positive, so this is equivalent). -/
theorem comparing_gaussian_tails (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (x y ε : ℝ)
    (hx : x ≤ 2) (hxy : |x - y| ≤ ε) :
    (1 - 8 * ε / (3 * σ ^ 2)) * (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici x)).toReal ≤
      (gaussianReal 0 (σ ^ 2).toNNReal (Set.Ici y)).toReal := by sorry

end SmoothedSimplex.Shadow
