-- Prove2me | Theorems.Thm_Rudin_ch08_parseval_L2_conv
-- name    : Rudin.ch08_parseval_L2_conv
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T12:37:17.033914+00:00
-- url     : https://prove2.me/theorems/269248a7-b216-4112-a804-4ca4ab3fe415
-- title:
--   Parseval's theorem, mean square convergence
-- statement:
--   Let $f: \mathbb{R} \to \mathbb{C}$ be a $2\pi$-periodic function such that $f$ and $|f|^2$ are Riemann-integrable on $[-\pi, \pi]$. Let $s_N(f; x)$ be the $N$-th partial sum of the Fourier series of $f$, and let $\|h\|_2 = \left( \frac{1}{2\pi} \int_{-\pi}^{\pi} |h(x)|^2 dx \right)^{1/2}$ be the $L^2$ norm. Then the Fourier series of $f$ converges to $f$ in the mean square sense:
--   $$ \lim_{N \to \infty} \|f - s_N(f)\|_2 = 0. $$
--   This is the completeness statement for the trigonometric system, relying on the fact that continuous periodic functions can be uniformly approximated by trigonometric polynomials (Theorem 8.15).
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, pp. 190-191, Theorem 8.16

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.16 (Parseval's theorem, part 1): the Fourier series of a Riemann-integrable
`2π`-periodic function `f` converges to `f` in the mean square sense. -/
theorem ch08_parseval_L2_conv (f : ℝ → ℂ) (hfper : HasPeriodTwoPi f)
    (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi) :
    Tendsto (fun N => L2Norm (fun x => f x - fourierPartialSum f N x)) atTop (𝓝 0) := by sorry

end Rudin
