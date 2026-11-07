-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalMonomialHolomorphicSum_mem
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalMonomialHolomorphicSum_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:20:01.694292+00:00
-- url     : https://prove2.me/theorems/937c5709-85e9-4c9f-bc94-a4c13cfa8957
-- title:
--   Tanner Lifted Product: lps Original Rational Monomial Holomorphic Sum mem
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rational Monomial Holomorphic Sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L366-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L366-L394

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalMonomialHolomorphicSum_mem
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : 0 < M)
    (u v : ι → ℕ) (a : ι → ℚ) :
    algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
      (lpsOriginalRationalMonomialHolomorphicSum M hM u v a) ∈
        lpsOriginalGeneratedFunctionFieldQ M hM := by sorry
