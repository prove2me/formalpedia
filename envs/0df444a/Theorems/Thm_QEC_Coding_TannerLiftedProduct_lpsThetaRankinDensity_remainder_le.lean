-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaRankinDensity_remainder_le
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_remainder_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:28:04.947784+00:00
-- url     : https://prove2.me/theorems/70eef489-201d-4159-be4e-6e5dded47fd8
-- title:
--   Tanner Lifted Product: lps Theta Rankin Density remainder le
-- statement:
--   The true theta-minus-complete-correction function contributes to the actual square density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L43-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L43-L47

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_remainder_le (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (τ : ℍ) :
    ‖lpsStandardTheta q τ-lpsThetaEisensteinCorrection q
      (by intro h;subst q;norm_num at hq4) τ‖^2*τ.im^2≤lpsThetaRankinDensity q hq4 τ := by sorry
