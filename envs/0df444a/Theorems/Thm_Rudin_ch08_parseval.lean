-- Prove2me | Theorems.Thm_Rudin_ch08_parseval
-- name    : Rudin.ch08_parseval
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T02:34:54.579964+00:00
-- url     : https://prove2.me/theorems/5efa43bd-6a6a-42b1-8d30-361bab5a0bd6
-- title:
--   Theorem 8.16 — Parseval's theorem
-- statement:
--   Let $f$ and $g$ be Riemann-integrable $2\pi$-periodic functions with Fourier coefficients $c_n$ and $\gamma_n$. Then $\|f - s_N(f)\|_2 \to 0$; $\frac{1}{2\pi}\int_{-\pi}^{\pi} f\bar g = \sum_n c_n\overline{\gamma_n}$; and, taking $g = f$, $\frac{1}{2\pi}\int_{-\pi}^{\pi}|f|^2 = \sum_n |c_n|^2$. The two-sided sums are the limits of the symmetric partial sums $\sum_{|n| \le N}$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 8, p. 191, Theorem 8.16

import Mathlib
import Definitions.Def_Rudin_ch08_fourier

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 8.16 (Parseval's theorem): for Riemann-integrable `2π`-periodic functions
`f` and `g` with Fourier coefficients `cₙ` and `γₙ`, the Fourier series of `f` converges to
`f` in the mean square sense, the inner products agree with the sum of `cₙ conj γₙ`, and
`(1/2π) ∫ |f|² = ∑ |cₙ|²`. -/
theorem ch08_parseval (f g : ℝ → ℂ) (hfper : HasPeriodTwoPi f) (hgper : HasPeriodTwoPi g)
    (hf : IntervalIntegrable f MeasureTheory.volume (-Real.pi) Real.pi)
    (hg : IntervalIntegrable g MeasureTheory.volume (-Real.pi) Real.pi)
    (hf2 : IntervalIntegrable (fun x => ‖f x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi)
    (hg2 : IntervalIntegrable (fun x => ‖g x‖ ^ 2) MeasureTheory.volume (-Real.pi) Real.pi) :
    Tendsto (fun N => L2Norm (fun x => f x - fourierPartialSum f N x)) atTop (𝓝 0) ∧
    Tendsto (fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        fourierCoeff f n * (starRingEnd ℂ) (fourierCoeff g n)) atTop
      (𝓝 ((1 / (2 * Real.pi) : ℂ) *
        ∫ x in (-Real.pi)..Real.pi, f x * (starRingEnd ℂ) (g x))) ∧
    Tendsto (fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ‖fourierCoeff f n‖ ^ 2) atTop
      (𝓝 ((1 / (2 * Real.pi)) * ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2)) := by sorry

end Rudin
