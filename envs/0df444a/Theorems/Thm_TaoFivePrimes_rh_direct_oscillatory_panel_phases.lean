-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_oscillatory_panel_phases
-- name    : TaoFivePrimes.rh_direct_oscillatory_panel_phases
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:30:37.117512+00:00
-- url     : https://prove2.me/theorems/1ffed5c6-ed7d-4bd9-bc3d-f16eab855324
-- title:
--   One explicit Taylor seed for all oscillatory panel phases
-- statement:
--   Let $|\tau|\le100$, and define
--
--   $$
--   P_\tau=\sum_{m=0}^{127}\frac{(3i\tau/512)^m}{m!},
--   \qquad c_j=\frac{3(2j+1)}{16}.
--   $$
--
--   For every integer $0\le j<16$,
--
--   $$
--   \left|e^{i\tau c_j}-P_\tau^{32(2j+1)}\right|\le 10^{-210}.
--   $$
--
--   For rational $\tau$, the real and imaginary parts of the displayed approximation are rational. This result supplies an exact phase approximation; it does not assert a zero-location result.
-- source:
--   The elementary exponential Taylor bound and the panel centers of the theta/Mellin quadrature framework due to Gabewhigham and sometik179.

import Mathlib

theorem TaoFivePrimes.rh_direct_oscillatory_panel_phases (τ : ℝ) (hτ : |τ|≤100) (i : ℕ) (hi : i<16) :
    ‖Complex.exp (Complex.I*(τ:ℂ)*(3*(2*(i:ℂ)+1)/16)) -
      (∑ m ∈ Finset.range 128,
        (Complex.I*((3*τ/512:ℝ):ℂ))^m/(m.factorial:ℂ))^(32*(2*i+1))‖ ≤ 1/10^210 := by sorry
