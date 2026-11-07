-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedCusp_support_sum
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_support_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:16:01.173196+00:00
-- url     : https://prove2.me/theorems/a80089d7-059f-42a8-8b78-c2ebe9570f70
-- title:
--   Tanner Lifted Product: lps Original Cleared Cusp support sum
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cleared Cusp support sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L555-L577
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L555-L577

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_support_sum
    (M B : ℕ) (P : Polynomial (Polynomial ℂ)) :
    lpsOriginalClearedCusp M B P =
      ∑ s : LPSOriginalBivariateSupport P, fun q =>
        (P.coeff s.1.val).coeff s.2.val *
          lpsOriginalClearedMonomial M B s.2.val s.1.val q := by sorry
