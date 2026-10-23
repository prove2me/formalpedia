-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_cqProcessing
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.cqProcessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:06:26.432088+00:00
-- url     : https://prove2.me/theorems/b7603f4f-4e3c-4f51-88f7-d379fa66d9c0
-- title:
--   Remark A.15: For measurable cq phi*, input P and CPTP psi*, I(P;psi*∘phi*)≤I(P;phi*), with I(P;phi*)=H(Pphi*)−H(phi*|P).
-- statement:
--   Let $W$ be a measurable map from an arbitrary measurable input space into the normalized states of a finite intrinsic system, let $P$ be any input probability measure, and let $\psi_*$ be a CPTP output operation. The average $PW$ and entropy averages are Bochner integrals of bounded measurable state functions. Define cq information by the mean divergence $\int D(W_x\Vert PW)\,dP(x)$.
--
--   $$
--   I(P;W)=H(PW)-\int H(W_x)\,dP(x),\qquad I(P;\psi_*\circ W)\le I(P;W).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 73, Remark A.15

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P40 (InBlocks)

attribute [local instance] QAlgorithms.Papers.Independent.Renew46.P43.matrixMeasurableSpace

/-- Remark A.15, PDF p.73: the entropy-difference identity and genuine channel
processing for arbitrary measurable input laws. Finite-dimensional normalized state
integrands are bounded, so their Bochner integrals are not totalized junk values. -/
theorem cqProcessing {X : Type*} [MeasurableSpace X] {Y Z : IntrinsicSystem}
    (mu : Measure X) [IsProbabilityMeasure mu]
    (W : X → Matrix (Fin Y.dim) (Fin Y.dim) ℂ) (hW : Measurable W)
    (hstates : ∀ x, Y.IsState (W x)) (T : IntrinsicOperation Z Y) :
    cqInformation mu W = ENNReal.ofReal
      (vnEntropy (cqAverage mu W) - ∫ x, vnEntropy (W x) ∂mu) ∧
    cqInformation mu (fun x => intrinsicRestriction Z T.map (W x)) ≤ cqInformation mu W := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
