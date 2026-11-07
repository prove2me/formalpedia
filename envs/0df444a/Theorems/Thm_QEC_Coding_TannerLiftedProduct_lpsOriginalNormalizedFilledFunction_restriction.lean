-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledFunction_restriction
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_restriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:07:43.654412+00:00
-- url     : https://prove2.me/theorems/d26ff407-9dd2-415f-8a66-6abf0be5fe6a
-- title:
--   Tanner Lifted Product: lps Original Normalized Filled Function restriction
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Normalized Filled Function restriction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizedIntegral.lean#L41-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizedIntegral.lean#L41-L60

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_restriction
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    lpsOriginalFilledMeromorphicRestriction N hN (lpsOriginalNormalizedFilledFunction N hN F)
      (lpsOriginalNormalizedFilledFunction_meromorphic N hN F hF) =
    lpsOriginalFilledMeromorphicRestriction N hN F hF := by sorry
