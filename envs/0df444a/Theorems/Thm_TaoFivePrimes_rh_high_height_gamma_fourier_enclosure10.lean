-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fourier_enclosure10
-- name    : TaoFivePrimes.rh_high_height_gamma_fourier_enclosure10
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:21:21.826323+00:00
-- url     : https://prove2.me/theorems/63bb36e6-5235-4b73-ae21-ea3a7487167b
-- title:
--   TaoFivePrimes.rh_high_height_gamma_fourier_enclosure10
-- statement:
--   All1954 required Fourier-integral samples of the actual normalized gamma moment of order10 are enclosed by the signed80-bit FFT outputs divided by32, with complex error at most10^(-15). This applies the accepted generic analytic bridge to exact accepted input, kernel, magnitude and convolution certificates. No endpoint sign, zero count or RH claim.
-- source:
--   Platt DOI10.1090/mcom/3198; Poisson summation and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive10
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_gamma_fourier_enclosure10 (m : Nat) (hm:m<1954) :
  let p:=RHHighZetaCorrelation.signed RHHighFFTPositive10.rows.flatten m
  ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 10) ((m:ℝ)/512)-
    ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^85‖≤1/10^15 := by sorry
