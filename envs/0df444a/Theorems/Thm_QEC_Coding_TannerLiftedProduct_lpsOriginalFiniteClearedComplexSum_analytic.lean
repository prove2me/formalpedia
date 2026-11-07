-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedComplexSum_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedComplexSum_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:20:38.259523+00:00
-- url     : https://prove2.me/theorems/2d99e830-138e-4d38-b1db-9ceb5e396f68
-- title:
--   Tanner Lifted Product: lps Original Finite Cleared Complex Sum analytic
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Finite Cleared Complex Sum analytic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L523-L529
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L523-L529

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedComplexSum_analytic
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : M ≠ 0)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℂ) :
    AnalyticAt ℂ (lpsOriginalFiniteClearedComplexSum M B u v a) 0 := by sorry
