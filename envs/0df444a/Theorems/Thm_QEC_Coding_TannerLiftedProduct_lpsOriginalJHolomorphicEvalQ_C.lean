-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJHolomorphicEvalQ_C
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJHolomorphicEvalQ_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:20:48.041718+00:00
-- url     : https://prove2.me/theorems/01159fd2-b58b-4a4f-8f26-40e81c22e9d9
-- title:
--   Tanner Lifted Product: lps Original JHolomorphic Eval Q C
-- statement:
--   The Tanner Lifted Product construction uses the lps Original JHolomorphic Eval Q C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L351-L357
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L351-L357

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJHolomorphicEvalQ_C (a : ℚ) :
    lpsOriginalJHolomorphicEvalQ (Polynomial.C a) =
      algebraMap ℚ LPSOriginalHolomorphicRing a := by sorry
