-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_direct_base_theta_jets
-- name    : TaoFivePrimes.rh_direct_base_theta_jets
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:38:54.267252+00:00
-- url     : https://prove2.me/theorems/e87ca3a2-d96f-47a5-9fb5-f44cdf2df052
-- title:
--   Certified base theta jets for direct oscillatory quadrature
-- statement:
--   Let
--
--   $$
--   B(z)=2e^{z/4}\sum_{n=1}^{8}e^{-\pi n^2e^z},
--   \qquad c_i=\frac{3(2i+1)}{16},\qquad h=\frac{3}{16},
--   $$
--
--   and let $q_{i,j}$ be the existing stored rational theta jet for panel $i$ and order $j$. For $0\le i<16$ and $0\le j<184$,
--
--   $$
--   \left|\frac{B^{(j)}(c_i)}{j!}h^j-q_{i,j}\right|\le10^{-234}.
--   $$
--
--   This places the existing theta-jet certification in the notation used by the direct oscillatory quadrature. Oscillatory convolution and zero-location conclusions require separate results.
-- source:
--   The published theta-jet data and certification framework are due to sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a; theta/Mellin foundations are due to Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHDirectOscillatoryQuadrature
import Definitions.Def_TaoFivePrimes_RHExtendedMomentRule
import Mathlib

theorem TaoFivePrimes.rh_direct_base_theta_jets (i : ℕ) (hi : i<16) (j : ℕ) (hj : j<184) :
    ‖(iteratedDeriv j (RHDirectOscillatory.kernel 0 0)
        ((3*(2*(i:ℝ)+1)/16:ℝ):ℂ)/(j.factorial:ℂ))*(3/16:ℂ)^j -
      ((RHNextMomentRule.jet i j:ℚ):ℂ)‖ ≤ 1/10^234 := by sorry
