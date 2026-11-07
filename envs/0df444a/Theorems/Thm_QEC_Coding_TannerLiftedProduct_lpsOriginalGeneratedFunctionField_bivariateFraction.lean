-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_bivariateFraction
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_bivariateFraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:21:04.878984+00:00
-- url     : https://prove2.me/theorems/2b2d7261-8878-4eac-989f-8ceab1181ad5
-- title:
--   Tanner Lifted Product: lps Original Generated Function Field bivariate Fraction
-- statement:
--   Every element of the genuine original generated field has an actual polynomial fraction with nonzero evaluated denominator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L51-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L51-L117

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_bivariateFraction
    (M : ℕ) (hM : 0 < M) (x : LPSOriginalHolomorphicFractionField)
    (hx : x ∈ lpsOriginalGeneratedFunctionField M hM) :
    ∃ G H : Polynomial (Polynomial ℂ),
      lpsOriginalBivariateHolomorphicEval M hM H ≠ 0 ∧
      x = algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
          (lpsOriginalBivariateHolomorphicEval M hM G) /
        algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
          (lpsOriginalBivariateHolomorphicEval M hM H) := by sorry
