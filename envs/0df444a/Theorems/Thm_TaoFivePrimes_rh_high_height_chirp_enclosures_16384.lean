-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_chirp_enclosures_16384
-- name    : TaoFivePrimes.rh_high_height_chirp_enclosures_16384
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T22:28:06.209782+00:00
-- url     : https://prove2.me/theorems/9048b866-badd-4847-9c38-4f40e8a18802
-- title:
--   TaoFivePrimes.rh_high_height_chirp_enclosures_16384
-- statement:
--   Every marked entry of the explicit 16384-point chirp table encloses exp(i*pi*q/16384) with complex norm error at most 1e-23. This proves actual transcendental accuracy of the 5463 needed integer proposals, using ordinary pi/Taylor/squaring/rounding proofs and kernel-checked finite arithmetic. It does not prove gamma samples, the complete FFT, endpoint signs or an RH zero count.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI 10.1090/mcom/3198, high-height Fourier architecture. Bluestein/chirp exact-convolution representation, positive-integer Horner evaluation of the complex exponential, and exact dyadic rounding. The pi enclosure and original numerical-method attribution are to sometik179 (c9908072-d99a-4431-aad8-a72c6352619a), with theta/Mellin foundations credited to Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighChirpData16384
import Theorems.Thm_TaoFivePrimes_rh_pi_enclosure_700

theorem TaoFivePrimes.rh_high_height_chirp_enclosures_16384 :
  ∀ q : Nat, q≤16384 → RHHighChirpCache.needed q=true →
  let v := RHHighChirpCache.expected.getD q ⟨0,0,0,0⟩
  ‖((v.r:ℂ)+(v.i:ℂ)*Complex.I)/(2:ℂ)^80-
    Complex.exp (Complex.I*((Real.pi*(q:ℝ)/16384:ℝ):ℂ))‖≤1/10^23 := by sorry
