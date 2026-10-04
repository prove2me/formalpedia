-- Prove2me | Theorems.Thm_TaoFivePrimes_eta0_dyadic_integral
-- name    : TaoFivePrimes.eta0_dyadic_integral
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T05:19:32.849232+00:00
-- url     : https://prove2.me/theorems/eb530449-d04a-447a-8d2d-4fc3dbe6c210
-- title:
--   Tao equation (eta0): the logarithmic cutoff as a dyadic average of window indicators
-- statement:
--   For all positive reals $x,d,w$,
--
--   $$\eta_0\!\left(\frac{dw}{x}\right)\ =\ 4\int_0^\infty \mathbf 1_{[\frac{x}{2W},\frac xW]}(d)\,\mathbf 1_{[\frac W2,W]}(w)\,\frac{dW}{W},$$
--
--   where $\eta_0(t)=4(\log2-|\log 2t|)_+$ is the source's logarithmic cutoff, supported on $[\tfrac14,1]$.
--
--   This is the identity that makes $\eta_0$ the right cutoff for the bilinear part of the argument: it exhibits the smooth weight $\eta_0(dw/x)$ attached to a product $dw$ as a dyadic average of products of two *independent* window indicators, one in $d$ and one in $w$. That is exactly what is needed to factorize the Type II sums, writing them as $4\int_0^\infty F(W)\frac{dW}{W}$ with each $F(W)$ a bilinear form over a pair of dyadic ranges, to which the large sieve applies.
--
--   The mechanism is that the two windows constrain $W$ to the interval between $\max(\frac{x}{2d},w)$ and $\min(\frac xd,2w)$, whose logarithmic length is $\log 4t$ for $\tfrac14\le t\le\tfrac12$, is $\log\frac1t$ for $\tfrac12\le t\le1$, and is negative — so the interval is empty — outside $[\tfrac14,1]$; these are the three branches of $\eta_0$.
--
--   **Formalization Note** The improper integral is the Lebesgue integral over $(0,\infty)$, and the product of the two indicators is written as a single conditional. The cutoff `eta0` is the platform definition, extended by zero to nonpositive arguments; the identity is stated for positive $x,d,w$, for which the argument $dw/x$ is positive.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 1 (Introduction), the identity labelled (eta0), displayed immediately after the definition (1.7) of eta_0 and used in Section 5 to factorize the Type II sums

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory Set

theorem TaoFivePrimes.eta0_dyadic_integral (x d w : ℝ) (hx : 0 < x) (hd : 0 < d) (hw : 0 < w) :
    4 * (∫ W in Set.Ioi (0 : ℝ),
        (if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then (1 : ℝ) / W else 0))
      = TaoFivePrimes.eta0 (d * w / x) := by sorry
