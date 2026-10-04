-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_weak_second_derivative_identity
-- name    : TaoFivePrimes.eta0_weak_second_derivative_identity
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:01:41.43802+00:00
-- url     : https://prove2.me/theorems/a9f40d6e-fe14-4e3c-8b60-e885487abfaf
-- title:
--   Weak second derivative of eta0 with all three jump atoms
-- statement:
--   Let $f$ be a twice continuously differentiable real function. The logarithmic triangular cutoff has weak second derivative
--
--   $$D^2\eta_0=-\frac4{t^2}\mathbf1_{(1/4,1/2)}\,dt+\frac4{t^2}\mathbf1_{(1/2,1)}\,dt+16\delta_{1/4}-16\delta_{1/2}+4\delta_1.$$
--
--   Concretely, this means
--
--   $$\int_{1/4}^1\eta_0(t)f''(t)\,dt=16f(1/4)-16f(1/2)+4f(1)+\int_{1/2}^1\frac4{t^2}f(t)\,dt-\int_{1/4}^{1/2}\frac4{t^2}f(t)\,dt.$$
--
--   This identity makes the jump contribution explicit in the distributional interpretation of Tao's norm $\|\eta_0''\|_1=48$, rather than silently identifying the classical second derivative with the whole distributional derivative. No compact support assumption on the test function is needed because every integral is over the fixed finite support interval. **Formalization Note:** the two derivatives are provided as functions with `HasDerivAt` hypotheses, and the second derivative is assumed continuous.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, definition (1.7), equation (5.13) and its following discussion of distributional derivatives and total variation, printed p.26. The displayed weak-derivative identity explicitly derives the distribution used there. https://arxiv.org/pdf/1201.6656

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory

theorem TaoFivePrimes.eta0_weak_second_derivative_identity (f f' f'' : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hc : Continuous f'') :
    (∫ t in (1 / 4 : ℝ)..1, TaoFivePrimes.eta0 t * f'' t) =
      16 * f (1 / 4) - 16 * f (1 / 2) + 4 * f 1 +
        (∫ t in (1 / 2 : ℝ)..1, (4 / t ^ 2) * f t) -
        (∫ t in (1 / 4 : ℝ)..(1 / 2), (4 / t ^ 2) * f t) := by sorry
