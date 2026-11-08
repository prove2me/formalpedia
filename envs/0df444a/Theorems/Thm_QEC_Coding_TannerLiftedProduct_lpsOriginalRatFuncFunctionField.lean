-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncFunctionField
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncFunctionField
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:34:31.452392+00:00
-- url     : https://prove2.me/theorems/9fb9acdb-ce3c-413c-a0db-2e924cc61c60
-- title:
--   Tanner Lifted Product: lps Original Rat Func Function Field
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rat Func Function Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalChartComparison.lean#L95-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalChartComparison.lean#L95-L103

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalChartComparison
set_option autoImplicit false
open QEC.Coding.TannerLiftedProduct
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
noncomputable section
local notation "P" => Polynomial ℂ
local notation "J" => FractionRing P
variable (N : ℕ) (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_3d79f03ea9_67
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_3d79f03ea9_70
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_3d79f03ea9_71
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_3d79f03ea9_72
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_3d79f03ea9_73
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_3d79f03ea9_77
variable [NeZero N]

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncFunctionField : _root_.FunctionField ℂ K := by sorry
