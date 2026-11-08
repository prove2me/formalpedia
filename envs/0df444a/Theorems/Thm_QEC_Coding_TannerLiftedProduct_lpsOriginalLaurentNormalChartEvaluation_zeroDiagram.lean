-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLaurentNormalChartEvaluation_zeroDiagram
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalLaurentNormalChartEvaluation_zeroDiagram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:21:40.490382+00:00
-- url     : https://prove2.me/theorems/dd705446-ef95-402a-8f2b-d3078b9dca84
-- title:
--   Tanner Lifted Product: lps Original Laurent Normal Chart Evaluation zero Diagram
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Laurent Normal Chart Evaluation zero Diagram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationOverlapEvaluation.lean#L102-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationOverlapEvaluation.lean#L102-L111

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationOverlapEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_9017904347_15
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_9017904347_16
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "ICL" => lpsOriginalComplexNormalLaurentChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_9017904347_22
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_9017904347_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_9017904347_24
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_9017904347_25

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalLaurentNormalChartEvaluation_zeroDiagram
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (hi : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    (lpsOriginalLaurentNormalChartEvaluation N hpos hN x hj hi).comp
      (lpsOriginalComplexNormalZeroToLaurent N hpos) =
        lpsOriginalZeroNormalChartEvaluation N hpos hN x hj := by sorry
