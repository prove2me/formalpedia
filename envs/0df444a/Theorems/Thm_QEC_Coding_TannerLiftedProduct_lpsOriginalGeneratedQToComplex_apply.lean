-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedQToComplex_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedQToComplex_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T03:59:40.921483+00:00
-- url     : https://prove2.me/theorems/673b5a8a-aad5-4e05-9e48-86277623b5bf
-- title:
--   Tanner Lifted Product: lps Original Generated QTo Complex apply
-- statement:
--   The inclusion preserves each literal holomorphic-fraction value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalArithmeticFunctionFieldComparison.lean#L116-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalArithmeticFunctionFieldComparison.lean#L116-L118

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedQToComplex_apply (N : ℕ) (hN : 0 < N)
    (x : lpsOriginalGeneratedFunctionFieldQ N hN) :
    (lpsOriginalGeneratedQToComplex N hN x).val = x.val := by sorry
