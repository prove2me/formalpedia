-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_fixed_point_multiply_error
-- name    : TaoFivePrimes.rh_direct_fixed_point_multiply_error
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:32:42.333632+00:00
-- url     : https://prove2.me/theorems/5dc607b3-ca64-4c82-a825-a547f901e075
-- title:
--   Error bound for rounded complex fixed-point multiplication
-- statement:
--   For a positive integer scale $D$ and integers $a,b,c,d$, define
--
--   $$
--   z=\frac{a+ib}{D},\quad w=\frac{c+id}{D},\quad
--   \widetilde{zw}=
--   \frac{\lfloor(ac-bd)/D\rfloor+i\lfloor(ad+bc)/D\rfloor}{D}.
--   $$
--
--   Then
--
--   $$
--   \left|\widetilde{zw}-zw\right|\le\frac{2}{D}.
--   $$
--
--   This estimate supports rigorous fixed-point evaluation of oscillatory phases and other complex arithmetic.
-- source:
--   Elementary Euclidean division and the triangle inequality, for the direct oscillatory theta quadrature experiment.

import Mathlib

theorem TaoFivePrimes.rh_direct_fixed_point_multiply_error (D : ℕ) (hD : 0<D) (a b c d : ℤ) :
    ‖(((a*c-b*d)/(D:ℤ):ℤ):ℂ)/(D:ℂ) +
       Complex.I*(((a*d+b*c)/(D:ℤ):ℤ):ℂ)/(D:ℂ) -
       (((a:ℂ)+Complex.I*(b:ℂ))/(D:ℂ))*(((c:ℂ)+Complex.I*(d:ℂ))/(D:ℂ))‖
       ≤ 2/(D:ℝ) := by sorry
