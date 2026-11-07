-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedComplexSum_taylor
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedComplexSum_taylor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:21:09.127202+00:00
-- url     : https://prove2.me/theorems/404cfb56-6846-46dc-b391-38f9a925d590
-- title:
--   Tanner Lifted Product: lps Original Finite Cleared Complex Sum taylor
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Finite Cleared Complex Sum taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L531-L545
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L531-L545

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedComplexSum_taylor
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : M ≠ 0)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℂ) :
    lpsOriginalTaylorSeries (lpsOriginalFiniteClearedComplexSum M B u v a) =
      ∑ i, PowerSeries.C (a i) * PowerSeries.map (algebraMap ℚ ℂ)
        (lpsOriginalClearedFormalMonomial M hM B (u i) (v i)) := by sorry
