-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRatFuncPolynomialTower
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncPolynomialTower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:33:08.456589+00:00
-- url     : https://prove2.me/theorems/d3e490ac-0fe0-4e8c-9fd0-1a772a19146a
-- title:
--   Tanner Lifted Product: lps Original Rat Func Polynomial Tower
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Rat Func Polynomial Tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalChartComparison.lean#L79-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalChartComparison.lean#L79-L84

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRatFuncPolynomialTower : IsScalarTower P (RatFunc ℂ) K := by sorry
