-- Prove2me | Theorems.Thm_TaoFivePrimes_smoothedExpSum_conj
-- name    : TaoFivePrimes.smoothedExpSum_conj
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-13T21:35:20.214273+00:00
-- url     : https://prove2.me/theorems/376f1e4f-bd8a-4dbb-aa20-20ccf2e79ee0
-- title:
--   Tao equation (4.5): self-adjointness of the smoothed prime exponential sum
-- statement:
--   For a cutoff $\eta$, a modulus $q_0$, a scale $x$ and a frequency $\alpha$, write
--
--   $$S_{\eta,q_0}(x,\alpha)\;=\;\sum_{n}\Lambda(n)\,e(\alpha n)\,\mathbf 1_{(n,q_0)=1}\,\eta\!\left(\frac nx\right),$$
--
--   where $\Lambda$ is the von Mangoldt function and $e(t)=e^{2\pi i t}$.
--
--   Because $\Lambda$ and $\eta$ are real valued, the sum is self-adjoint in the frequency:
--
--   $$S_{\eta,q_0}(x,-\alpha)\;=\;\overline{S_{\eta,q_0}(x,\alpha)} .$$
--
--   This symmetry halves the work on the circle: it is what lets the source restrict attention to $0\le\alpha\le\tfrac12$ in Sections 5, 6 and 8.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, equation (4.5)

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

theorem TaoFivePrimes.smoothedExpSum_conj (eta : ℝ → ℝ) (q₀ : ℕ) (x alpha : ℝ) :
    TaoFivePrimes.smoothedExpSum eta q₀ x (-alpha)
      = (starRingEnd ℂ) (TaoFivePrimes.smoothedExpSum eta q₀ x alpha) := by sorry
