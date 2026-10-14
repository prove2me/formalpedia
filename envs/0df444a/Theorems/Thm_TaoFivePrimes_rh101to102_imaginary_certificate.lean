-- Prove2me | Theorems.Thm_TaoFivePrimes_rh101to102_imaginary_certificate
-- name    : TaoFivePrimes.rh101to102_imaginary_certificate
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-14T05:00:55.82211+00:00
-- url     : https://prove2.me/theorems/085a0a7f-b2f9-40a6-a16f-0cf5dbba435f
-- title:
--   TaoFivePrimes.rh101to102_imaginary_certificate
-- statement:
--   The imaginary part of the proposed rounded local polynomial has absolute value at least the distance to the critical line on the lower half-rectangle, heights 101 to 101.5. The full real coordinate range [0,1] and both height endpoints are included. This is a finite polynomial certificate; analytic coefficient accuracy and RH are separate conclusions.
-- source:
--   Exact-rational continuation of sometik179's theta/Mellin and polynomial method, original c9908072-d99a-4431-aad8-a72c6352619a and accepted ordinary-syntax pilot 30db8e24-e604-49d7-ab5c-f7b6f516651a; theta/Mellin foundations attributed to Gabewhigham. New finite tensor Bernstein tables and polynomial identities are verified by ordinary Lean proofs.

import Definitions.Def_TaoFivePrimes_RHLocalRoundedPolynomial
import Definitions.Def_TaoFivePrimes_RH101To102RoundedCoefficients

theorem TaoFivePrimes.rh101to102_imaginary_certificate (s : ℂ) (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1) (ha : 101 ≤ s.im) (hb : s.im ≤ 203/2) :
    |s.re-1/2| ≤ |(TaoFivePrimes_RHLocalRoundedPolynomial TaoFivePrimes_RH101To102RoundedCoefficients 32 (203/2) s).im| := by sorry
