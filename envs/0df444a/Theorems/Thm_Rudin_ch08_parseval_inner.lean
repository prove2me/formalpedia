-- Prove2me | Theorems.Thm_Rudin_ch08_parseval_inner
-- name    : Rudin.ch08_parseval_inner
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T12:37:21.060631+00:00
-- url     : https://prove2.me/theorems/c49c3f99-571d-461e-8ebe-a1879a08db5a
-- title:
--   Parseval's identity for inner products
-- statement:
--   Let $f, g: \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic functions such that $f, g, |f|^2, |g|^2$ are Riemann-integrable on $[-\pi, \pi]$. Let $c_n$ and $\gamma_n$ be their respective Fourier coefficients. Then the $L^2$ inner product of $f$ and $g$ is given by the absolutely convergent sum of the products of their Fourier coefficients:
--   $$ \frac{1}{2\pi} \int_{-\pi}^{\pi} f(x) \overline{g(x)} dx = \sum_{n=-\infty}^{\infty} c_n \overline{\gamma_n}. $$
--   This identity follows directly from the mean square convergence of the Fourier series.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, p. 191, Theorem 8.16

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.16 (Parseval's theorem, part 2): for Riemann-integrable `2π`-periodic functions
`f` and `g`, the inner product is the sum of the products of their Fourier coefficients. -/
theorem ch08_parseval_inner (f g : ℝ → ℂ) (hfper : HasPeriodTwoPi f) (hgper : HasPeriodTwoPi g)
    (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable g MeasureTheory.volume (-Real.pi) Real.pi)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi)
    (hg2 : IntervalIntegrable (fun x => ‖g x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi) :
    Tendsto (fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        fourierCoeff f n * (starRingEnd ℂ) (fourierCoeff g n)) atTop
      (𝓝 ((1 / (2 * Real.pi) : ℂ) *
        ∫ x in (-Real.pi)..Real.pi, f x * (starRingEnd ℂ) (g x))) := by sorry

end Rudin
