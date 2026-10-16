-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_batch01_height_contour_fft_semantic
-- name    : TaoFivePrimes.rh_batch01_height_contour_fft_semantic
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-15T18:38:41.83023+00:00
-- url     : https://prove2.me/theorems/5c0c2f4f-92f8-4b24-bf05-9b0a2f0086f5
-- title:
--   TaoFivePrimes.rh_batch01_height_contour_fft_semantic
-- statement:
--   Generic analytic interpretation of a proposed sparse contour FFT. Exact input identities and integer magnitude bounds, rational-reference comparisons and component bounds imply that every decoded output approximates the explicit polynomial normalized Taylor coefficient by at most10^(-12). The reference exponential, reciprocal, eighth-root and dyadic recurrence errors and the Bluestein convolution are all proved. This is a supporting analytic theorem and makes no endpoint sign, winding, zero count or RH conclusion.
-- source:
--   Platt DOI10.1090/mcom/3198; Bluestein convolution and finite exponential Taylor bounds. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib
import Definitions.Def_TaoFivePrimes_RHBatch01PolynomialJet
import Definitions.Def_TaoFivePrimes_RHHighContourVector
import Definitions.Def_TaoFivePrimes_RHBatch01ContourCoefficient
import Definitions.Def_TaoFivePrimes_RHHighFFTArithmeticBase
import Definitions.Def_TaoFivePrimes_RHHighPackedFFT

theorem TaoFivePrimes.rh_batch01_height_contour_fft_semantic (t : Fin 3) (k : Nat) (hk:k<8) (v : List Nat)
    (ar ai : Fin 16384→Nat) (br bi : Fin 32767→Nat)
    (hAr:∀ j,ar j≤2^167) (hAi:∀ j,ai j≤2^167)
    (hBr:∀ j,br j≤2^82) (hBi:∀ j,bi j≤2^82)
    (hzero:RHHighContourVector.value (RHHighContourVector.decode ((v[0]?).getD 0))=
      if k=0 then RHBatch01FourierPolynomial.coefficient 0 else 0)
    (hc:∀positive:Bool,∀m:Nat,1 ≤ m ∧ m≤1024 →
      let a:=RHBatch01ContourCoefficientData.coefficient t positive m k
      let b:=RHBatch01ContourCoefficientData.proposed v positive m
      |a.1-b.1*2^48|≤(2:Int)^52 ∧ |a.2-b.2*2^48|≤(2:Int)^52)
    (hmag:∀positive:Bool,∀m:Nat,1 ≤ m ∧ m≤1024 →
      let b:=RHBatch01ContourCoefficientData.proposed v positive m
      |b.1|+|b.2|≤(2:Int)^80)
    (hinput:∀ j:Fin 16384,RHHighContourVector.raw v RHHighFFTArithmeticBase.chirp j.val=
      ((ar j:Int)-2^166,(ai j:Int)-2^166))
    (hkernel:∀ j:Fin 32767,
      ((br j:Int)-2^81,(bi j:Int)-2^81)=
      RHHighFFTArithmeticBase.chirp ((j.val:Int)-16383).natAbs)
    (r : Fin 2048) :
    ‖RHBatch01PolynomialJet.jet (64*(t.val:ℂ)-64+(1/2:ℂ)*Complex.I+(r.val:ℂ)/32) (1/32) k-
        (let p:=((RHHighPackedFFT.output (List.ofFn ar) (List.ofFn ai)
          (List.ofFn br) (List.ofFn bi) (List.ofFn (fun j=>br j+bi j))
          RHHighFFTArithmeticBase.chirp)[r.val]?).getD (0,0)
         ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^80)‖≤1/10^12 := by sorry
