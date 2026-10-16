-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_kernel_gamma_fft_uniform_analytic
-- name    : TaoFivePrimes.rh_fast_kernel_gamma_fft_uniform_analytic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T20:25:45.863035+00:00
-- url     : https://prove2.me/theorems/d50165db-5370-48cc-b505-da9a50afed82
-- title:
--   TaoFivePrimes.rh_fast_kernel_gamma_fft_uniform_analytic
-- statement:
--   Uniform analytic gamma-moment FFT interpretation for every natural center3000000256≤T≤3999999744,k<26. Under exact chirped input/kernel identities and explicit integer magnitude bounds, the first1954 Fourier samples differ from the decoded packed transform by≤1e-15. Reuses the public uniform moment theorem; all FFT, Bluestein, Poisson, and alias-tail lemmas are included explicitly. Actual arrays, endpoint signs, zero counting and RH remain separate.
-- source:
--   Platt Fourier construction, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Bluestein convolution and Poisson summation. Mathematics carried from the accepted fixed-center gamma FFT semantic proof, with the final Poisson/input/sample bridges parameterized and only published formal theorem interfaces imported. Original surrounding work: sometik179 c9908072-d99a-4431-aad8-a72c6352619a; Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighSamplingFunctions
import Definitions.Def_TaoFivePrimes_RHFastKernelNormalizedMomentArithmetic
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT
open scoped FourierTransform

theorem TaoFivePrimes.rh_fast_kernel_gamma_fft_uniform_analytic (T : Nat) (hT : 3000000256≤T) (hU : T≤3999999744) (k : Nat) (hk:k<26)
    (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat)
    (hAr:∀ j,ar j≤2^167) (hAi:∀ j,ai j≤2^167)
    (hBr:∀ j,br j≤2^82) (hBi:∀ j,bi j≤2^82)
    (hinput:∀ j:Fin 16384,
      let m:=RHFastKernelMomentArithmetic.moment j.val (RHFastKernelGammaArithmetic.compute T j.val) k
      let c:=RHHighFFTArithmeticBase.chirp j.val
      (m.1*c.1+m.2*c.2,m.2*c.1-m.1*c.2)=
      ((ar j:Int)-2^166,(ai j:Int)-2^166))
    (hkernel:∀ j:Fin 32767,
      ((br j:Int)-2^81,(bi j:Int)-2^81)=
      RHHighFFTArithmeticBase.chirp ((j.val:Int)-16383).natAbs)
    (m : Fin 2048) (hm:m.val≤1953) :
    ‖𝓕 (RHHighSamplingFunctions.moment (T:ℝ) k) ((m.val:ℝ)/512)-
      Complex.exp (((2*Real.pi*((m.val:ℝ)/2):ℝ):ℂ)*Complex.I)*((1/32:ℂ)*
        (let v:=((RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai)
          (List.ofFn br) (List.ofFn bi) (List.ofFn (fun j=>br j+bi j))
          RHHighFFTArithmeticBase.chirp)[m.val]?).getD (0,0)
         ((v.1:ℂ)+(v.2:ℂ)*Complex.I)/(2:ℂ)^80))‖≤1/10^15 := by sorry
