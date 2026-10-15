-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_high_height_real_fft_semantic
-- name    : TaoFivePrimes.rh_high_height_real_fft_semantic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T09:18:55.711671+00:00
-- url     : https://prove2.me/theorems/9ce5648a-2215-4973-ac24-dd3b363037c3
-- title:
--   TaoFivePrimes.rh_high_height_real_fft_semantic
-- statement:
--   Actual real-axis polynomial values are enclosed by the exact Bluestein output to1e-12, provided the finite128-bit root products,80-bit coefficient rounding, chirped inputs and kernel identities hold. Proves analytic root enclosure, sparse polynomial DFT identity, input perturbation and accepted FFT error composition. No zeta sign, winding, count or RH assertion.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHHighContourCoefficient
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT
import Definitions.Def_TaoFivePrimes_RHHighFourierPolynomial

theorem TaoFivePrimes.rh_high_height_real_fft_semantic (t : Fin 3) (v : List Nat)
 (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat)
 (hAr:∀j,ar j≤2^167) (hAi:∀j,ai j≤2^167) (hBr:∀j,br j≤2^82) (hBi:∀j,bi j≤2^82)
 (hz:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=RHHighFourierPolynomial.coefficient 0)
 (hc:∀positive:Bool,∀m:Nat,1 ≤ m ∧ m≤1024 →
  let p:=RHHighContourVector.coefficient v positive m
  let q:=RHHighContourCoefficientData.mul (RHHighContourCoefficientData.inputCoefficient m positive)
   (RHHighContourUnit.pair (RHHighContourCoefficientData.rootIndex t positive m))
  p=(q.1/(2:Int)^48,q.2/(2:Int)^48))
 (hi:∀j:Fin 16384,RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp j.val=((ar j:Int)-2^166,(ai j:Int)-2^166))
 (hker:∀j:Fin 32767,((br j:Int)-2^81,(bi j:Int)-2^81)=RHHighFFTArithmeticBase.chirp ((j.val:Int)-16383).natAbs)
 (r : Fin 2048) :
 ‖RHHighFourierPolynomial.polynomial (64*((t.val:ℂ)-1)+(r.val:ℂ)/32)-
  RHHighContourVector.value (((RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai)
   (List.ofFn br) (List.ofFn bi) (List.ofFn (fun j=>br j+bi j)) RHHighFFTArithmeticBase.chirp)[r.val]?).getD (0,0))‖≤1/10^12 := by sorry
