-- Prove2me | Theorems.Thm_TaoFivePrimes_smoothedExpSum_le_deriv_L1_mul_sharp
-- name    : TaoFivePrimes.smoothedExpSum_le_deriv_L1_mul_sharp
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:41:32.788883+00:00
-- url     : https://prove2.me/theorems/b740d08f-bfd5-4825-b9b7-5b56297391ec
-- title:
--   Tao Lemma 4.2: replacing a smooth cutoff by the sharp truncation costs $\|\eta'\|_{L^1}$
-- statement:
--   For a cutoff $\eta$, a modulus $q_0$, a scale $x$ and a frequency $\alpha$, write
--
--   $$S_{\eta,q_0}(x,\alpha)\;=\;\sum_{n}\Lambda(n)\,e(\alpha n)\,\mathbf 1_{(n,q_0)=1}\,\eta\!\left(\frac nx\right),$$
--
--   where $\Lambda$ is the von Mangoldt function and $e(t)=e^{2\pi i t}$.
--
--   Let $\eta$ be smooth, compactly supported and vanishing on $[1,\infty)$, and let $x\ge1$. Suppose the unsmoothed partial sums are uniformly bounded by $B$:
--
--   $$\Bigl|\sum_{n\le N}\Lambda(n)\,e(\alpha n)\,\mathbf 1_{(n,q_0)=1}\Bigr|\;\le\;B\qquad\text{for every }N\le x .$$
--
--   Then
--
--   $$\bigl|S_{\eta,q_0}(x,\alpha)\bigr|\;\le\;\|\eta'\|_{L^1(\mathbb R)}\;B .$$
--
--   This is the transfer principle that lets an estimate for the sharp-cutoff exponential sum be carried over to the smoothed one, at the cost of the total variation of the cutoff. It is how the minor-arc bounds of Section 5, which are proved for sharp cutoffs, are applied to the smoothed sums used elsewhere.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, Lemma 4.2

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open MeasureTheory

theorem TaoFivePrimes.smoothedExpSum_le_deriv_L1_mul_sharp
    (eta : ℝ → ℝ) (q₀ : ℕ) (x alpha B : ℝ)
    (hx : 1 ≤ x) (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hcs : HasCompactSupport eta)
    (hsupp : ∀ t : ℝ, 1 ≤ t → eta t = 0)
    (hB : ∀ N : ℕ, N ≤ ⌊x⌋₊ →
      ‖∑ n ∈ Finset.range (N+1),
        (if Nat.Coprime n q₀ then
          (ArithmeticFunction.vonMangoldt n : ℂ) * TaoFivePrimes.expCircle (alpha * n)
         else 0)‖ ≤ B) :
    ‖TaoFivePrimes.smoothedExpSum eta q₀ x alpha‖
      ≤ (∫ u : ℝ, |deriv eta u|) * B := by sorry
