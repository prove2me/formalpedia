-- Prove2me | Theorems.Thm_Rudin_ch08_parseval_norm
-- name    : Rudin.ch08_parseval_norm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T12:37:32.186265+00:00
-- url     : https://prove2.me/theorems/c14baf2a-0032-427f-9da1-f0eeee57a608
-- title:
--   Parseval's identity for norms
-- statement:
--   Let $f: \mathbb{R} \to \mathbb{C}$ be a $2\pi$-periodic function such that $f$ and $|f|^2$ are Riemann-integrable on $[-\pi, \pi]$. Let $c_n$ be its Fourier coefficients. Then the sum of the squared moduli of the Fourier coefficients equals the mean square norm of $f$:
--   $$ \sum_{n=-\infty}^{\infty} |c_n|^2 = \frac{1}{2\pi} \int_{-\pi}^{\pi} |f(x)|^2 dx. $$
--   This is the special case of the inner product Parseval identity when $g = f$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, p. 191, Theorem 8.16

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.16 (Parseval's theorem, part 3): for Riemann-integrable `2π`-periodic `f`,
the sum of the squared moduli of its Fourier coefficients equals its mean square norm. -/
theorem ch08_parseval_norm (f : ℝ → ℂ) (hfper : HasPeriodTwoPi f)
    (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖fourierCoeff f n‖ ^ 2) atTop
      (𝓝 ((1 / (2 * Real.pi)) * ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2)) := by sorry

end Rudin
