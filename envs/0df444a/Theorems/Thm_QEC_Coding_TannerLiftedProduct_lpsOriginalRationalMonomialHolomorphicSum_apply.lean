-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalMonomialHolomorphicSum_apply
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalMonomialHolomorphicSum_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:21:47.881248+00:00
-- url     : https://prove2.me/theorems/0281a60c-4794-4ede-96d9-f29315d0ded3
-- title:
--   Tanner Lifted Product: lps Original Rational Monomial Holomorphic Sum apply
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rational Monomial Holomorphic Sum apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L283-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalLevelInclusion.lean#L283-L302

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalMonomialHolomorphicSum_apply
    {ι : Type*} [Fintype ι] (M : ℕ) (hM : 0 < M)
    (u v : ι → ℕ) (a : ι → ℚ) (τ : ℍ) :
    (lpsOriginalRationalMonomialHolomorphicSum M hM u v a).val τ =
      ∑ i, (a i : ℂ) * lpsOriginalJInvariant τ ^ u i *
        lpsOriginalJDilated M hM τ ^ v i := by sorry
