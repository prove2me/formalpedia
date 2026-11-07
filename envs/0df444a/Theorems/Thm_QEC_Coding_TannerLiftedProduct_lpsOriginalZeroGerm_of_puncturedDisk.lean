-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroGerm_of_puncturedDisk
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalZeroGerm_of_puncturedDisk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:16:02.178839+00:00
-- url     : https://prove2.me/theorems/9ce374c5-3052-4ba2-9dfd-61b01a429e22
-- title:
--   Tanner Lifted Product: lps Original Zero Germ of punctured Disk
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Zero Germ of punctured Disk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L396-L413
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L396-L413

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalZeroGerm_of_puncturedDisk
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hz : ∀ q : ℂ, ‖q‖ < 1 → q ≠ 0 → f q = 0) :
    f =ᶠ[𝓝 0] 0 := by sorry
