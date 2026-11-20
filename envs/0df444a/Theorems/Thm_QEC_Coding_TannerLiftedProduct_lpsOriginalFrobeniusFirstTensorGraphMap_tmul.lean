-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFrobeniusFirstTensorGraphMap_tmul
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFrobeniusFirstTensorGraphMap_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:52:38.170311+00:00
-- url     : https://prove2.me/theorems/e470b207-da25-4990-8ad5-e0db11148d90
-- title:
--   Tanner Lifted Product: lps Original Frobenius First Tensor Graph Map tmul
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Frobenius First Tensor Graph Map tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L212-L216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointFiber.lean#L212-L216

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusFiber
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFrobeniusFirstTensorGraphMap_tmul
    (p : ℕ) (K : Type*) [Field K] [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] (a b : K) :
    lpsOriginalFrobeniusFirstTensorGraphMap p K (a ⊗ₜ[ZMod p] b) = a * b^p := by sorry
