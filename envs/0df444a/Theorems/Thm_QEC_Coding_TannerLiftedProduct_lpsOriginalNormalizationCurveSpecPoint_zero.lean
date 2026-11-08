-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizationCurveSpecPoint_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizationCurveSpecPoint_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:29:06.744285+00:00
-- url     : https://prove2.me/theorems/68853851-dd3c-4e7d-8f1c-249f9e80506d
-- title:
--   Tanner Lifted Product: lps Original Normalization Curve Spec Point zero
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Normalization Curve Spec Point zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationComplexPoints.lean#L133-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationComplexPoints.lean#L133-L139

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationOverlapEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationComplexPoints
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_18
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_19
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_24
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_25
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_26
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffe444fe3b_27

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizationCurveSpecPoint_zero (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) :
    lpsOriginalNormalizationCurveSpecPoint N hpos hN x =
      lpsOriginalZeroNormalizationSpecPoint N hpos hN x hj ≫
        lpsOriginalComplexNormalGluedChartMap N hpos false := by sorry
