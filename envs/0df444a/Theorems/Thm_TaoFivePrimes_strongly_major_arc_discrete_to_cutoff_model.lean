-- Prove2me | Theorems.Thm_TaoFivePrimes_strongly_major_arc_discrete_to_cutoff_model
-- name    : TaoFivePrimes.strongly_major_arc_discrete_to_cutoff_model
-- status  : Open
-- author  : @marwahaha
-- created : 2026-09-09T09:07:46.694984+00:00
-- url     : https://prove2.me/theorems/c78fd776-bb76-45ac-a6f4-78fd9213d230
-- title:
--   Strongly major arc: reduction to the cutoff convolution
-- statement:
--   For an integer $x\ge 87\cdot10^{35}$, set
--   $$
--   M=\frac{x^2}{1000}\left\lfloor\frac{4\cdot10^{14}}3\right\rfloor^3
--   $$
--   and define the full-line cutoff coefficient
--   $$
--   C=\int_{\mathbb R}\int_{\mathbb R}
--    \eta_1(s)\eta_1\!\left(1-s-\frac{t}{1000}\right)\eta_0(t)\,ds\,dt.
--   $$
--   Let $I(x)$ be the integral of Tao's finite circle-method representation integrand over the closed central arc
--   $$
--   \|\alpha\|\le \frac{3.29\cdot10^9}{3.6\pi x}.
--   $$
--   Prove the explicit approximation
--   $$
--   |I(x)-MC|\le 0.09M.
--   $$
--   This statement isolates the analytic part of Proposition 8.3: the verified-RH major-arc approximations for the three prime sums, removal of the primorial sieve factors, approximation of the positive-shift kernel, the two Cauchy--Schwarz error integrals, and the Fourier tail. It retains the cutoff convolution $C$ exactly, so its normalization is handled separately.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997–1038; arXiv:1201.6656v4, Section 8, Proposition 8.3 and equations (8.12)–(8.16), pp. 32–35. https://arxiv.org/html/1201.6656v4#S8. This child stops at the exact cutoff convolution before the source normalization slip. It uses the corrected N0/3 in (8.13), alpha*x/K in the eta0 Fourier factor, and central radius T0/(3.6*pi*x). The 0.09 budget safely contains the source analytic errors while excluding the separate cutoff-mass correction.

import Definitions.Def_TaoFivePrimes_FourierRepresentation
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

namespace TaoFivePrimes

theorem strongly_major_arc_discrete_to_cutoff_model (x : ℕ)
    (h1 : 87 * 10 ^ 35 ≤ x) :
    let scale : ℝ :=
      (x : ℝ) ^ 2 / 1000 * ((4 * 10 ^ 14 / 3 : ℕ) : ℝ) ^ 3
    let cutoffCoefficient : ℂ :=
      ∫ t : ℝ, ∫ s : ℝ,
        (((eta1 s * eta1 (1 - s - t / 1000) * eta0 t : ℝ) : ℂ))
    ‖(∫ α in Metric.closedBall (0 : AddCircle (1 : ℝ))
            (3.29 * 10 ^ 9 / (3.6 * Real.pi * (x : ℝ))),
          representationIntegrand x (4 * 10 ^ 14) α
            ∂AddCircle.haarAddCircle) -
        (scale : ℂ) * cutoffCoefficient‖ ≤
      9 / 100 * scale := by sorry

end TaoFivePrimes
