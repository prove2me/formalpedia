-- Prove2me | Theorems.Thm_TaoFivePrimes_eta_cutoff_truncated_real_fourier_source
-- name    : TaoFivePrimes.eta_cutoff_truncated_real_fourier_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-09T15:34:14.699182+00:00
-- url     : https://prove2.me/theorems/252904b8-1ec7-47b4-946d-c0bee68d4d48
-- title:
--   Truncated real Fourier inversion for the Section 8 cutoffs
-- statement:
--   Let $F_1$ and $F_0$ be the positive-phase real Fourier transforms of Tao's literal cutoffs $\eta_1$ and $\eta_0$, and put $U=T_0/(3.6\pi)$. The integral of $F_1(u)^2F_0(u/1000)e(-u)$ over $[-U,U]$ differs by at most $0.01$ from the physical-space convolution $\iint \eta_1(s)\eta_1(1-s-t/1000)\eta_0(t)\,ds\,dt$. This is the real-line Fourier inversion identity together with the explicit truncated-tail estimate used in Section 8.
-- source:
--   Terence Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 8, displays following (8.16), especially the Fourier tail estimate and physical-space convolution displays (corresponding to the HTML displays S8.Ex21 and S8.Ex23), https://arxiv.org/abs/1201.6656

import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory

namespace TaoFivePrimes

theorem eta_cutoff_truncated_real_fourier_source :
    let U : ℝ := 3.29 * 10 ^ 9 / (3.6 * Real.pi)
    let F1 : ℝ → ℂ := fun u =>
      ∫ s : ℝ, (eta1 s : ℂ) * expCircle (u * s)
    let F0 : ℝ → ℂ := fun u =>
      ∫ t : ℝ, (eta0 t : ℂ) * expCircle (u * t)
    let cutoffCoefficient : ℂ :=
      ∫ t : ℝ, ∫ s : ℝ,
        (((eta1 s * eta1 (1 - s - t / 1000) * eta0 t : ℝ) : ℂ))
    ‖(∫ u in Set.Icc (-U) U,
          F1 u ^ 2 * F0 (u / 1000) * expCircle (-u)) -
        cutoffCoefficient‖ ≤ (1 / 100 : ℝ) := by sorry

end TaoFivePrimes
