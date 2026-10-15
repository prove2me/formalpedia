-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_gamma_fft_semantic
-- name    : TaoFivePrimes.rh_high_height_gamma_fft_semantic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T06:51:06.957304+00:00
-- url     : https://prove2.me/theorems/3d51ea0e-ae80-4bc3-9b7b-b51e1d999b1c
-- title:
--   TaoFivePrimes.rh_high_height_gamma_fft_semantic
-- statement:
--   Generic analytic interpretation of the exact16384-sample gamma moment FFT: under exact chirped input identities, kernel identities and explicit integer magnitude bounds, the first1954 Fourier integral values differ from the decoded output by at most10^(-15). The proof combines accepted gamma/chirp enclosures, exact integer convolution soundness, Bluestein factorization and Poisson summation with rigorous time/frequency alias tails. This is a supporting analytic theorem and makes no endpoint sign, zero count or RH conclusion.
-- source:
--   Platt DOI10.1090/mcom/3198; Poisson summation and Bluestein convolution. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHHighNormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT
open scoped FourierTransform

theorem TaoFivePrimes.rh_high_height_gamma_fft_semantic (k : Nat) (hk:k<26)
    (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat)
    (hAr:∀ j,ar j≤2^167) (hAi:∀ j,ai j≤2^167)
    (hBr:∀ j,br j≤2^82) (hBi:∀ j,bi j≤2^82)
    (hinput:∀ j:Fin 16384,
      let m:=RHHighMomentArithmetic.moment j.val (RHHighGammaArithmetic.compute j.val) k
      let c:=RHHighFFTArithmeticBase.chirp j.val
      (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)=
      ((ar j:Int)-2^166,(ai j:Int)-2^166))
    (hkernel:∀ j:Fin 32767,
      ((br j:Int)-2^81,(bi j:Int)-2^81)=
      RHHighFFTArithmeticBase.chirp ((j.val:Int)-16383).natAbs)
    (m : Fin 2048) (hm:m.val≤1953) :
    ‖𝓕 (RHHighSamplingFunctions.moment 3289999936 k) ((m.val:ℝ)/512)-
      Complex.exp (((2*Real.pi*((m.val:ℝ)/2):ℝ):ℂ)*Complex.I)*((1/32:ℂ)*
        (let v:=((RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai)
          (List.ofFn br) (List.ofFn bi) (List.ofFn (fun j=>br j+bi j))
          RHHighFFTArithmeticBase.chirp)[m.val]?).getD (0,0)
         ((v.1:ℂ)+(v.2:ℂ)*Complex.I)/(2:ℂ)^80))‖≤1/10^15 := by sorry
