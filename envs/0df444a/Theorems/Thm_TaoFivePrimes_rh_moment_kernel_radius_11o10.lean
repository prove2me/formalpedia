-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_moment_kernel_radius_11o10
-- name    : TaoFivePrimes.rh_moment_kernel_radius_11o10
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:03:52.756852+00:00
-- url     : https://prove2.me/theorems/48e35044-000a-40de-8226-7d25cbd92ba5
-- title:
--   Wider Cauchy bound for the truncated theta moment kernel
-- statement:
--   For a nonnegative integer $k$, let
--
--   $$
--   K_k(z)=2e^{z/4}\frac{(64z)^k}{k!}\sum_{n=0}^{7}e^{-\pi(n+1)^2e^z}.
--   $$
--
--   If $c\ge0$ and $|z-c|\le11/10$, then
--
--   $$
--   |K_k(z)|\le11\cdot10^{84}.
--   $$
--
--   The bound holds uniformly in $k$ and supports rigorous Taylor quadrature on the existing sixteen panels.
-- source:
--   A wider Cauchy-circle estimate for the theta/Mellin framework developed by sometik179 and Gabewhigham; it uses the separately proved sine-square interval enclosure.

import Mathlib

theorem TaoFivePrimes.rh_moment_kernel_radius_11o10 (k : ℕ) (c : ℝ) (hc : 0≤c) (z : ℂ)
    (hz : ‖z-(c:ℂ)‖ ≤ (11/10:ℝ)) :
    ‖2*Complex.exp (z/4)*((64*z)^k/(k.factorial:ℂ))*
      (∑ n ∈ Finset.range 8, Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z))‖ ≤ 11*10^84 := by sorry
