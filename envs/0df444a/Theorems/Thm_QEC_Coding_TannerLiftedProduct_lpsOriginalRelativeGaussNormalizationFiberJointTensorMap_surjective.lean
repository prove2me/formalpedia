-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_surjective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:52:06.014185+00:00
-- url     : https://prove2.me/theorems/ba864649-8025-4d69-ad96-7037de55f7b6
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization Fiber Joint Tensor Map surjective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization Fiber Joint Tensor Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L179-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L179-L197

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalizationFiberJointTensorMap_surjective
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Function.Surjective
      (lpsOriginalRelativeGaussNormalizationFiberJointTensorMap N p hNp h4N hN hpN q) := by sorry
