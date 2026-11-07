-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_level_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_level_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:13:23.916741+00:00
-- url     : https://prove2.me/theorems/0ea07cdf-437f-4926-82cf-bdc13787e889
-- title:
--   Tanner Lifted Product: lps Original Generated Function Field Q level le
-- statement:
--   Same-original rational level inclusion, constructed from genuine complex pullback and rational descent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L709-L726
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L709-L726

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFullFieldLevelPullback
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeFunctionFieldDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalLevelInclusion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_level_le
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) (hN : 4 ∣ N)
    (hposN : 0 < N) (hposM : 0 < M) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalGeneratedFunctionFieldQ N hposN ≤
      lpsOriginalGeneratedFunctionFieldQ M hposM := by sorry
