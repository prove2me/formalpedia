-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedRationalSum_taylor
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedRationalSum_taylor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:15:56.941203+00:00
-- url     : https://prove2.me/theorems/f3285b50-2e2f-4616-8d4d-d19dab75b7fb
-- title:
--   Tanner Lifted Product: lps Original Finite Cleared Rational Sum taylor
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Finite Cleared Rational Sum taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L317-L333
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L317-L333

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedRationalSum_taylor
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : M ≠ 0)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℚ) :
    lpsOriginalTaylorSeries (lpsOriginalFiniteClearedRationalSum M B u v a) =
      PowerSeries.map (algebraMap ℚ ℂ)
        (∑ i, PowerSeries.C (a i) * lpsOriginalClearedFormalMonomial M hM B (u i) (v i)) := by sorry
