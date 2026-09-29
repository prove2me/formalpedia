-- Prove2me | Theorems.Thm_TaoFivePrimes_smoothedExpSum_zero_asymptotic
-- name    : TaoFivePrimes.smoothedExpSum_zero_asymptotic
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T23:13:49.320966+00:00
-- url     : https://prove2.me/theorems/d8f92251-9022-4f67-8439-fe9e2d3c1177
-- title:
--   Tao Lemma 4.3 (4.4): S_{eta,1}(x,0) = x*int(eta) + O*(||eta'||_1 x / (40 log cx))
-- statement:
--   For a cutoff $\eta$, a modulus $q$, a scale $x$ and a frequency $\alpha$, write
--
--   $$S_{\eta,q}(x,\alpha)\;=\;\sum_{n}\Lambda(n)\,e(\alpha n)\,\mathbf 1_{(n,q)=1}\,\eta\!\left(\frac nx\right),$$
--
--   $\Lambda$ being the von Mangoldt function. Let $\eta$ be smooth and supported in $[c,1]$ for some $0<c\le 1$, and let $x\ge1$ satisfy $cx\ge10^{8}$. Then
--
--   $$S_{\eta,1}(x,0)\;=\;x\int_{\mathbb R}\eta\;+\;\mathcal O^{*}\!\left(\frac{\|\eta'\|_{L^{1}(\mathbb R)}\,x}{40\log(cx)}\right),$$
--
--   where $\mathcal O^{*}(E)$ denotes a quantity of absolute value at most $E$. For the non-negative cutoffs used in the paper the main term $x\int_{\mathbb R}\eta$ is the $\|\eta\|_{L^{1}(\mathbb R)}x$ of the source.
--
--   The estimate is what converts the prime-counting content of $S_{\eta,1}(x,0)$ into the analytic quantity $x\int\eta$; together with the trivial bound (4.3) of the same lemma it underlies the mass computations of Sections 4 and 8.
--
--   **Quoted input** The proof in the source invokes the explicit Chebyshev estimate of Rosser and Schoenfeld, $\psi(y)=y+\mathcal O^{*}\bigl(y/(40\log cx)\bigr)$ for $cx\le y\le x$, where $\psi(y)=\sum_{n\le y}\Lambda(n)$. That estimate is not available in the ambient library, so it appears as an explicit hypothesis, stated exactly in the range and the form in which it is used.
--
--   **Formalization Note** The sum $S_{\eta,q}(x,\alpha)$ is complex-valued; at $\alpha=0$ it is a real number embedded in $\mathbb C$, and the error is measured by the complex absolute value.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, Lemma 4.3, equation (4.4)

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

theorem TaoFivePrimes.smoothedExpSum_zero_asymptotic
    (eta : ℝ → ℝ) (hsm : ContDiff ℝ (⊤ : ℕ∞) eta) (c x : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hx : 1 ≤ x)
    (hsupp : ∀ t : ℝ, t < c ∨ 1 < t → eta t = 0)
    (hcx : (10 : ℝ) ^ 8 ≤ c * x)
    (hpsi : ∀ y : ℝ, c * x ≤ y → y ≤ x →
      |Chebyshev.psi y - y| ≤ y / (40 * Real.log (c * x))) :
    ‖TaoFivePrimes.smoothedExpSum eta 1 x 0 - (((∫ t : ℝ, eta t) * x : ℝ) : ℂ)‖
      ≤ 1 / (40 * Real.log (c * x)) * (∫ t : ℝ, |deriv eta t|) * x := by sorry
