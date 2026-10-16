-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure18
-- name    : TaoFivePrimes.rh_high_height_gamma_fourier_enclosure18
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T11:57:08.397908+00:00
-- url     : https://prove2.me/theorems/8379a31e-a299-4bb6-93d4-16334fa5a28b
-- title:
--   TaoFivePrimes.rh_high_height_gamma_fourier_enclosure18
-- statement:
--   All1954 required Fourier-integral samples of the actual normalized gamma moment of order18 are enclosed by the signed80-bit FFT outputs divided by32, with complex error at most10^(-15). This applies the accepted generic analytic bridge to exact accepted input, kernel, magnitude and convolution certificates. No endpoint sign, zero count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198; Poisson summation and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive18
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_gamma_fourier_enclosure18 (m : Nat) (hm:m<1954) :
  let p:=RHHighZetaCorrelation.signed RHHighFFTPositive18.rows.flatten m
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 18) ((m:ℝ)/512)-
    ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^85‖≤1/10^15 := by sorry
