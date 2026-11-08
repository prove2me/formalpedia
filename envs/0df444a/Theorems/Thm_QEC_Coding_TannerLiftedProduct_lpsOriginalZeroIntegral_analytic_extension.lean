-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroIntegral_analytic_extension
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalZeroIntegral_analytic_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:08:37.508735+00:00
-- url     : https://prove2.me/theorems/d372e855-6abc-4795-be42-a7225e8797b4
-- title:
--   Tanner Lifted Product: lps Original Zero Integral analytic extension
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Zero Integral analytic extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalMeromorphicOrder.lean#L195-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLocalMeromorphicOrder.lean#L195-L213

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLocalChartGermTopology
variable (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_125
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_131
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_132
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_133
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_135
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4f02bb1b4c_136

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalZeroIntegral_analytic_extension
    (x : LPSOriginalFilledCurve N)
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (a : integralClosure P K) :
    ∃ F : LPSOriginalFilledMeromorphicFunctionRing N hN,
      lpsOriginalCompactMeromorphicGermAlgHom N hN F =
        lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN a.val ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g (lpsOriginalLocalChartCenter N hN x) ∧
        F.val ∘ (lpsOriginalLocalChart N hN x).symm =ᶠ[𝓝[≠] lpsOriginalLocalChartCenter N hN x] g := by sorry
