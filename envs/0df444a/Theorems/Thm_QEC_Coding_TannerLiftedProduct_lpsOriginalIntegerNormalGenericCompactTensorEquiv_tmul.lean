-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerNormalGenericCompactTensorEquiv_tmul
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGenericCompactTensorEquiv_tmul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T03:59:51.838881+00:00
-- url     : https://prove2.me/theorems/daf5bd6e-a8b1-44b9-9b98-3e2e2205f985
-- title:
--   Tanner Lifted Product: lps Original Integer Normal Generic Compact Tensor Equiv tmul
-- statement:
--   The arithmetic tensor comparison preserves the genuine generic-stalk function values.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalArithmeticFunctionFieldComparison.lean#L305-L329
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalArithmeticFunctionFieldComparison.lean#L305-L329

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGenericCompactTensorEquiv_tmul
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalIntegerNormalGluedScheme_integral N hpos
    letI := (lpsOriginalIntegerNormalGenericJFractionEmbedding N hpos).toAlgebra
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    ∀ (r : FractionRing (Polynomial ℂ))
      (x : (lpsOriginalIntegerNormalGluedScheme N hpos).functionField),
    lpsOriginalIntegerNormalGenericCompactTensorEquiv N hpos hN
      (r ⊗ₜ[FractionRing (Polynomial ℚ)] x) =
      r • lpsOriginalGeneratedCompactMeromorphicAlgEquiv N hpos hN
        (lpsOriginalGeneratedQToComplex N hpos
          (lpsOriginalIntegerNormalGenericFunctionFieldAlgEquiv N hpos x)) := by sorry
