-- Prove2me | Theorems.Thm_TaoFivePrimes_oscillatory_smoothed_zero_kernel_bound
-- name    : TaoFivePrimes.oscillatory_smoothed_zero_kernel_bound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T21:36:03.128708+00:00
-- url     : https://prove2.me/theorems/0dd3cdac-8716-407b-99ed-60e0433ac373
-- title:
--   Sine-sensitive bound for the double-box zero kernel
-- statement:
--   Let $a,h>0$ with $2h\le a$, and let $\rho=\beta+i\gamma$ satisfy $0\le\beta\le1$ and $\gamma\ne0$. For the double-box zero kernel
--
--   $$
--   K(a,h,\rho)=\frac{(a+2h)^{\rho+2}-2(a+h)^{\rho+2}+a^{\rho+2}}{h^2\rho(\rho+1)(\rho+2)},
--   $$
--
--   put $r=h/(a+h)$. Then
--
--   $$
--   |K(a,h,\rho)|\le\frac{(a+2h)^{\beta+2}}{h^2|\gamma|^3}
--   \left(4\sin^2(\gamma r/2)+8r+3|\gamma|r^2\right).
--   $$
--
--   This retains the oscillation in the central second difference instead of replacing it by its maximum value.
-- source:
--   The double-box zero kernel is the published Dusart smoothing formalization, attributed there to Pierre Dusart, Estimates of Some Functions Over Primes without R.H., Theorem 45 and Lemmas 47–55. The sine-sensitive inequality is an elementary supporting estimate developed for the Tao five-primes Chebyshev-error reduction.

import Definitions.Def_dusart_psi_433_20261014_SmoothedFormula
import Mathlib.Tactic

theorem TaoFivePrimes.oscillatory_smoothed_zero_kernel_bound
    (a h : ℝ) (ρ : ℂ) (ha : 0 < a) (hh : 0 < h) (hsmall : 2*h ≤ a)
    (hβ0 : 0 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hγ : 0 < |ρ.im|) :
    ‖DusartSmoothing.smoothedZeroKernel a h ρ‖ ≤
      (a+2*h)^(ρ.re+2)/(h^2*|ρ.im|^3) *
        (4*(Real.sin (ρ.im*(h/(a+h))/2))^2 + 8*(h/(a+h)) +
          3 * |ρ.im| * (h/(a+h))^2) := by sorry
