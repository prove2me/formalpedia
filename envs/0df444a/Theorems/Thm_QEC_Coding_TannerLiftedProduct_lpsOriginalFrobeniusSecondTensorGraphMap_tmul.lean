-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFrobeniusSecondTensorGraphMap_tmul
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFrobeniusSecondTensorGraphMap_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:52:05.625623+00:00
-- url     : https://prove2.me/theorems/6596d772-4e0d-4c84-8afe-7cb0ccdcc72d
-- title:
--   Tanner Lifted Product: lps Original Frobenius Second Tensor Graph Map tmul
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Frobenius Second Tensor Graph Map tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L218-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L218-L222

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFrobeniusSecondTensorGraphMap_tmul
    (p : ℕ) (K : Type*) [Field K] [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] (a b : K) :
    lpsOriginalFrobeniusSecondTensorGraphMap p K (a ⊗ₜ[ZMod p] b) = a^p * b := by sorry
