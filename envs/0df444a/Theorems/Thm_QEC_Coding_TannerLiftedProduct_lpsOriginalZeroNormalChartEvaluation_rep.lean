-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroNormalChartEvaluation_rep
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalZeroNormalChartEvaluation_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:19:19.040023+00:00
-- url     : https://prove2.me/theorems/f831094e-b30a-4bd8-b378-dcad2bcb0b71
-- title:
--   Tanner Lifted Product: lps Original Zero Normal Chart Evaluation rep
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Zero Normal Chart Evaluation rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationChartEvaluation.lean#L51-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalNormalizationChartEvaluation.lean#L51-L64

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AnalyticGermEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_18
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_19
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "IC0" => lpsOriginalComplexNormalZeroChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_26
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_27
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_28
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_30
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_bb7e6d852b_31

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalZeroNormalChartEvaluation_rep
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (a : IC0) (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val)
    (g : ℂ → ℂ) (hg : AnalyticAt ℂ g (lpsOriginalLocalChartCenter N hN x))
    (he : F.val ∘ (lpsOriginalLocalChart N hN x).symm =ᶠ[𝓝[≠] lpsOriginalLocalChartCenter N hN x] g) :
    lpsOriginalZeroNormalChartEvaluation N hpos hN x hj a = g (lpsOriginalLocalChartCenter N hN x) := by sorry
