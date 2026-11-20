-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaRankinDensity_continuous
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:29:05.569179+00:00
-- url     : https://prove2.me/theorems/83a80c89-5ed7-4acb-a8a5-5bcc419f275c
-- title:
--   Tanner Lifted Product: lps Theta Rankin Density continuous
-- statement:
--   The actual LPS theta square density is continuous.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L24-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L24-L27

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_continuous (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    Continuous (lpsThetaRankinDensity q hq4) := by sorry
