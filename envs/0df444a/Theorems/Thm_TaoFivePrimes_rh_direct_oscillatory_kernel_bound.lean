-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_oscillatory_kernel_bound
-- name    : TaoFivePrimes.rh_direct_oscillatory_kernel_bound
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:24:28.80227+00:00
-- url     : https://prove2.me/theorems/2a016517-f2e8-4ee9-b46e-05a9da9b998b
-- title:
--   Uniform Cauchy bound for a direct oscillatory theta kernel
-- statement:
--   For $\tau\in\mathbb R$ and $k\ge0$, let
--
--   $$
--   K_{\tau,k}(z)=2e^{z/4}\frac{z^k}{k!}e^{i\tau z}\sum_{n=0}^{7}e^{-\pi(n+1)^2e^z}.
--   $$
--
--   If $|\tau|\le100$, $0\le c\le6$, and $|z-c|\le11/10$, then
--
--   $$
--   |K_{\tau,k}(z)|\le10^{59}.
--   $$
--
--   This uniform bound supports direct oscillatory quadrature near positive zeta heights up to 200; it is not a zero-location theorem.
-- source:
--   Direct oscillatory version of the theta/Mellin framework due to sometik179 and Gabewhigham, using the separately proved sine-square interval enclosure.

import Mathlib

theorem TaoFivePrimes.rh_direct_oscillatory_kernel_bound (τ : ℝ) (hτ : |τ| ≤ 100) (k : ℕ) (c : ℝ)
    (hc0 : 0≤c) (hc1 : c≤6) (z : ℂ) (hz : ‖z-(c:ℂ)‖ ≤ (11/10:ℝ)) :
    ‖2*Complex.exp (z/4)*(z^k/(k.factorial:ℂ))*Complex.exp (Complex.I*(τ:ℂ)*z)*
      (∑ n ∈ Finset.range 8, Complex.exp (-(Real.pi:ℂ)*(n+1)^2*Complex.exp z))‖ ≤ 10^59 := by sorry
