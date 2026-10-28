-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_verified_slice_107_107p35
-- name    : TaoFivePrimes.rh_verified_slice_107_107p35
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:58:28.234227+00:00
-- url     : https://prove2.me/theorems/c4151e8e-edde-468d-b57c-2b285a1fd40e
-- title:
--   Critical-line location for zeta zeros at heights 107–107.35
-- statement:
--   Every zero $s=\sigma+it$ of the Riemann zeta function in the open critical strip $0<\sigma<1$ and with height $107\le t\le107.35$ lies on the critical line:
--
--   $$
--   \sigma=\tfrac12.
--   $$
--
--   The endpoints are included, and the assertion makes no simplicity assumption. This slice contains a low-lying critical-line zero and extends the finite-height verification used in the five-primes mission.
-- source:
--   Derived here from the certified height-106.5 local xi approximation and the new imaginary-part Bernstein certificate. The analytic projection method is adapted from Prove2Me submission 016f4991-59da-4657-a24d-de763fabf1a4 by sometik179, with theta/Mellin foundations by Gabewhigham. The finite RH verification follows from Theorem 1.5 of Tao, arXiv:1201.6656v4, https://arxiv.org/abs/1201.6656, and the numerical verification of Platt, Math. Comp. 86 (2017), 2449–2467.

import Mathlib.NumberTheory.LSeries.RiemannZeta

theorem TaoFivePrimes.rh_verified_slice_107_107p35 (s : ℂ) (hs : riemannZeta s = 0) (h0 : 0 < s.re) (h1 : s.re < 1)
    (ha : 107 ≤ s.im) (hb : s.im ≤ (2147/20:ℝ)) : s.re = 1/2 := by sorry
