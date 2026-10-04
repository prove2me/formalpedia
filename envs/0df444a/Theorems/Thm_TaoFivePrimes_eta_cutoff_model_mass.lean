-- Prove2me | Theorems.Thm_TaoFivePrimes_eta_cutoff_model_mass
-- name    : TaoFivePrimes.eta_cutoff_model_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-09T09:07:45.038363+00:00
-- url     : https://prove2.me/theorems/fe792adc-e64b-4f34-acf3-aa1a412545c9
-- title:
--   Mass of the shifted cutoff convolution
-- statement:
--   For Tao's cutoffs
--   $$
--   \eta_0(t)=4(\log 2-|\log(2t)|)_+,
--   \qquad
--   \eta_1(t)=(1-10\,\mathrm{dist}(t,[0.2,0.8]))_+,
--   $$
--   prove that the shifted autocorrelation coefficient
--   $$
--   C=\int_{\mathbb R}\int_{\mathbb R}
--    \eta_1(s)\eta_1\!\left(1-s-\frac{t}{1000}\right)\eta_0(t)\,ds\,dt
--   $$
--   satisfies
--   $$
--   \left|C-\frac23\right|\le 0.01.
--   $$
--   Indeed, symmetry gives the unshifted value $\int\eta_1^2=2/3$. Since $\eta_1$ is $10$-Lipschitz, $\eta_0$ is a nonnegative unit-mass cutoff supported on $[1/4,1]$, and $\int\eta_1=7/10$, the translation changes the coefficient by at most $(10/1000)(7/10)=0.007$.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, Mathematics of Computation 83 (2014), 997–1038; arXiv:1201.6656v4, equations (1.7), (8.1)–(8.5), and the cutoff-convolution calculation following (8.16), pp. 32 and 35. https://arxiv.org/html/1201.6656v4#S8. The paper incorrectly centers this convolution at 1; its own equation (8.2) gives integral eta1^2 = 2/3. The formal statement uses the corrected center 2/3 and the literal K=1000 cutoffs.

import Definitions.Def_TaoFivePrimes_RepresentationCount
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

namespace TaoFivePrimes

theorem eta_cutoff_model_mass :
    let cutoffCoefficient : ℂ :=
      ∫ t : ℝ, ∫ s : ℝ,
        (((eta1 s * eta1 (1 - s - t / 1000) * eta0 t : ℝ) : ℂ))
    ‖cutoffCoefficient - (((2 / 3 : ℝ) : ℂ))‖ ≤ 1 / 100 := by sorry

end TaoFivePrimes
