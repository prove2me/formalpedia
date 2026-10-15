-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_vector_fft_semantic
-- name    : TaoFivePrimes.rh_high_height_vector_fft_semantic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T07:25:37.331977+00:00
-- url     : https://prove2.me/theorems/a285f0e3-1161-43e6-a28f-7de6219bccb1
-- title:
--   TaoFivePrimes.rh_high_height_vector_fft_semantic
-- statement:
--   The ordinary integer packed convolution output approximates the explicit discrete Fourier transform of any proposed sparse vector bounded by18, with error at most10^(-13). All packing, convolution, rounding and chirp errors are proved. Makes no analytic polynomial, sign, count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_high_height_vector_fft_semantic (v : List Nat) (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat)
    (hAr:∀ j,ar j≤2^167) (hAi:∀ j,ai j≤2^167)
    (hBr:∀ j,br j≤2^82) (hBi:∀ j,bi j≤2^82)
    (hmag:∀j:Fin 16384,‖RHHighContourVector.value (RHHighContourVector.vector v j.val)‖≤18)
    (hinput:∀ j:Fin 16384,RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp j.val=
      ((ar j:Int)-2^166,(ai j:Int)-2^166))
    (hkernel:∀ j:Fin 32767,
      ((br j:Int)-2^81,(bi j:Int)-2^81)=
      RHHighFFTArithmeticBase.chirp ((j.val:Int)-16383).natAbs)
    (r : Fin 2048) :
    ‖(∑j:Fin 16384,RHHighContourVector.value (RHHighContourVector.vector v j.val)*
       Complex.exp (((Real.pi*(-2*(j.val:ℝ)*(r.val:ℝ)/16384):ℝ):ℂ)*Complex.I))-
      (let p:=(((RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai)
        (List.ofFn br) (List.ofFn bi) (List.ofFn (fun j=>br j+bi j))
        RHHighFFTArithmeticBase.chirp)[r.val]?).getD (0,0))
       ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^80)‖≤1/10^13 := by sorry
