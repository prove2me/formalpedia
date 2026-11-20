-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaRankinDensity_nonneg
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:28:21.501179+00:00
-- url     : https://prove2.me/theorems/309feed5-35be-400a-b255-dc3a8f71274f
-- title:
--   Tanner Lifted Product: lps Theta Rankin Density nonneg
-- statement:
--   The actual LPS theta square density is nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L30-L33
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L30-L33

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_nonneg (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (τ : ℍ) :
    0≤lpsThetaRankinDensity q hq4 τ := by sorry
