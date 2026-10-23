-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_holevoBound
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.holevoBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T07:07:08.405573+00:00
-- url     : https://prove2.me/theorems/5dc36cd6-bd0f-40bf-bf40-b217a9ac9d91
-- title:
--   Theorem A.16: For cq phi*, law P and measurement D, I(P;D*∘phi*)≤I(P;phi*).
-- statement:
--   Let $W$ be a measurable state-valued channel on a finite intrinsic output system, $P$ any input probability measure, and $D$ an actual finite or countable POVM. The measured information is the integral of the divergence between its conditional and marginal outcome laws; the right side is the cq mean state divergence.
--
--   $$
--   I(P;D_*\circ W)\le I(P;W).
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 37, Theorem A.16

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

/-- Theorem A.16, PDF pp.37,73: Holevo's bound for the actual measurement outcome
law, allowing countable outcomes and arbitrary measurable input distributions. -/
theorem holevoBound {X B : Type*} [MeasurableSpace X] [Countable B] {Y : IntrinsicSystem}
    (mu : Measure X) [IsProbabilityMeasure mu]
    (W : X → Matrix (Fin Y.dim) (Fin Y.dim) ℂ) (hW : Measurable W)
    (hstates : ∀ x, Y.IsState (W x))
    (D : B → Matrix (Fin Y.dim) (Fin Y.dim) ℂ) (hD : IsCountablePOVM D)
    (hblocks : ∀ b, InBlocks Y.block (D b)) :
    cqMeasuredInformation mu W D ≤ cqInformation mu W := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
