-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalCompactMeromorphicTensorEquiv_jN
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalCompactMeromorphicTensorEquiv_jN
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T03:59:13.24385+00:00
-- url     : https://prove2.me/theorems/1561d357-d663-47e8-9a7c-db155f2055b8
-- title:
--   Tanner Lifted Product: lps Original Rational Compact Meromorphic Tensor Equiv j N
-- statement:
--   The tensor of the same original j_N is the genuine global germ of filled j_N.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalArithmeticFunctionFieldComparison.lean#L218-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalArithmeticFunctionFieldComparison.lean#L218-L260

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalCompactMeromorphicTensorEquiv_jN
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    letI := (lpsOriginalCompactMeromorphicJFractionEmbedding N hN).toAlgebra
    let αQ : lpsOriginalGeneratedFunctionFieldQ N hpos :=
      ⟨lpsOriginalJNInFractionField N hpos,
        IntermediateField.subset_adjoin (FractionRing (Polynomial ℚ))
          {lpsOriginalJNInFractionField N hpos} (Set.mem_singleton _)⟩
    (lpsOriginalRationalCompactMeromorphicTensorEquiv N hpos hN
      ((1 : FractionRing (Polynomial ℂ)) ⊗ₜ[FractionRing (Polynomial ℚ)] αQ)).val =
      (lpsOriginalFilledJDilated N hpos :
        Filter.Germ (Filter.codiscrete (LPSOriginalFilledCurve N)) ℂ) := by sorry
