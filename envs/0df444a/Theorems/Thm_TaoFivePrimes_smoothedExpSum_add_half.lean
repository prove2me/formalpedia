-- Prove2me | Theorems.Thm_TaoFivePrimes_smoothedExpSum_add_half
-- name    : TaoFivePrimes.smoothedExpSum_add_half
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:35:18.957622+00:00
-- url     : https://prove2.me/theorems/19bb30bf-1bfa-4c68-8504-6230dc229267
-- title:
--   Tao equation (4.6): anti-symmetry of the smoothed sum for an even modulus
-- statement:
--   For a cutoff $\eta$, a modulus $q_0$, a scale $x$ and a frequency $\alpha$, write
--
--   $$S_{\eta,q_0}(x,\alpha)\;=\;\sum_{n}\Lambda(n)\,e(\alpha n)\,\mathbf 1_{(n,q_0)=1}\,\eta\!\left(\frac nx\right),$$
--
--   where $\Lambda$ is the von Mangoldt function and $e(t)=e^{2\pi i t}$.
--
--   If the modulus $q_0$ is even, then only odd $n$ contribute, and $e\bigl(n(\alpha+\tfrac12)\bigr)=-e(\alpha n)$ for such $n$. Hence
--
--   $$S_{\eta,q_0}\bigl(x,\alpha+\tfrac12\bigr)\;=\;-\,S_{\eta,q_0}(x,\alpha) .$$
--
--   This anti-symmetry is the degenerate case $p=2$ of Montgomery's uncertainty principle (Lemma 4.4), and it is what makes the frequency $\tfrac12$ behave like the frequency $0$ in the major-arc analysis.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, equation (4.6)

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

theorem TaoFivePrimes.smoothedExpSum_add_half (eta : ℝ → ℝ) (q₀ : ℕ) (hq : 2 ∣ q₀)
    (x alpha : ℝ) :
    TaoFivePrimes.smoothedExpSum eta q₀ x (alpha + 1/2)
      = - TaoFivePrimes.smoothedExpSum eta q₀ x alpha := by sorry
