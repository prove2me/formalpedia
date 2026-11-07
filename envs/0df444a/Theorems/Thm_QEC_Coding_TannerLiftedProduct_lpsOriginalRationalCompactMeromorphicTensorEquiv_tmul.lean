-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalCompactMeromorphicTensorEquiv_tmul
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalCompactMeromorphicTensorEquiv_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:09:11.145248+00:00
-- url     : https://prove2.me/theorems/d02fc604-d2c8-49d7-9a3f-2e1c329c2472
-- title:
--   Tanner Lifted Product: lps Original Rational Compact Meromorphic Tensor Equiv tmul
-- statement:
--   The full compact-field comparison preserves the actual pure-tensor values.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalArithmeticFunctionFieldComparison.lean#L203-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalArithmeticFunctionFieldComparison.lean#L203-L215

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelFunctionField
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalArithmeticFunctionFieldComparison
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6e81b77173_97
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6e81b77173_99
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6e81b77173_101
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_6e81b77173_103

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalCompactMeromorphicTensorEquiv_tmul
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
    (r : FractionRing (Polynomial ℂ)) (x : lpsOriginalGeneratedFunctionFieldQ N hpos) :
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    lpsOriginalRationalCompactMeromorphicTensorEquiv N hpos hN
      (r ⊗ₜ[FractionRing (Polynomial ℚ)] x) =
        r • lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN
          (lpsOriginalGeneratedQToComplex N hpos x) := by sorry
