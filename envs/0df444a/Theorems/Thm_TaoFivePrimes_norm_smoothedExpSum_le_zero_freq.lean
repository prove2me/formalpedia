-- Prove2me | Theorems.Thm_TaoFivePrimes_norm_smoothedExpSum_le_zero_freq
-- name    : TaoFivePrimes.norm_smoothedExpSum_le_zero_freq
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:35:25.062582+00:00
-- url     : https://prove2.me/theorems/06f0362c-d2e5-4ac8-9847-013f91915945
-- title:
--   Tao equation (4.2): the trivial bound at a general frequency
-- statement:
--   For a cutoff $\eta$, a modulus $q_0$, a scale $x$ and a frequency $\alpha$, write
--
--   $$S_{\eta,q_0}(x,\alpha)\;=\;\sum_{n}\Lambda(n)\,e(\alpha n)\,\mathbf 1_{(n,q_0)=1}\,\eta\!\left(\frac nx\right),$$
--
--   where $\Lambda$ is the von Mangoldt function and $e(t)=e^{2\pi i t}$.
--
--   If $\eta$ is non-negative and vanishes on $(1,\infty)$, and $x\ge1$, then the sum is largest at the zero frequency:
--
--   $$\bigl|S_{\eta,q_0}(x,\alpha)\bigr|\;\le\;S_{\eta,q_0}(x,0)\qquad\text{for every }\alpha .$$
--
--   This is the trivial bound quoted throughout Sections 4 and 8 whenever no cancellation in the exponential is available; it is what reduces the $L^\infty$ estimates on the minor arc to a comparison against the total mass $S_{\eta,q_0}(x,0)$.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, equation (4.2)

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

theorem TaoFivePrimes.norm_smoothedExpSum_le_zero_freq (eta : ℝ → ℝ) (q₀ : ℕ) (x alpha : ℝ)
    (hx : 1 ≤ x) (heta : ∀ t : ℝ, 0 ≤ eta t) (hsupp : ∀ t : ℝ, 1 < t → eta t = 0) :
    ‖TaoFivePrimes.smoothedExpSum eta q₀ x alpha‖
      ≤ ‖TaoFivePrimes.smoothedExpSum eta q₀ x 0‖ := by sorry
