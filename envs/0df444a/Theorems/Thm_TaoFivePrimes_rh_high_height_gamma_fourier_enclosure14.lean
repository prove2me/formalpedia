-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure14
-- name    : TaoFivePrimes.rh_high_height_gamma_fourier_enclosure14
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:45:24.892963+00:00
-- url     : https://prove2.me/theorems/0251f60b-0b11-4e47-a223-16b755b3c8dc
-- title:
--   TaoFivePrimes.rh_high_height_gamma_fourier_enclosure14
-- statement:
--   All1954 required Fourier-integral samples of the actual normalized gamma moment of order14 are enclosed by the signed80-bit FFT outputs divided by32, with complex error at most10^(-15). This applies the accepted generic analytic bridge to exact accepted input, kernel, magnitude and convolution certificates. No endpoint sign, zero count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198; Poisson summation and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive14
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_gamma_fourier_enclosure14 (m : Nat) (hm:m<1954) :
  let p:=RHHighZetaCorrelation.signed RHHighFFTPositive14.rows.flatten m
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 14) ((m:ℝ)/512)-
    ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^85‖≤1/10^15 := by sorry
