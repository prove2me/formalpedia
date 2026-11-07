-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFiniteClearedRationalSum_formal_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedRationalSum_formal_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:20:07.849557+00:00
-- url     : https://prove2.me/theorems/94ed88fc-9ba0-4042-9df7-f273292d2c23
-- title:
--   Tanner Lifted Product: lps Original Finite Cleared Rational Sum formal ne zero
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Finite Cleared Rational Sum formal ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L415-L438
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L415-L438

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFiniteClearedRationalSum_formal_ne_zero
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : 0 < M)
    (B : ℕ) (u v : ι → ℕ) (a : ι → ℚ)
    (hB : ∀ i, u i + M * v i ≤ B)
    (hs : (∑ i, PowerSeries.C (a i) *
      lpsOriginalClearedFormalMonomial M (Nat.ne_of_gt hM) B (u i) (v i)) ≠ 0) :
    lpsOriginalRationalMonomialHolomorphicSum M hM u v a ≠ 0 := by sorry
