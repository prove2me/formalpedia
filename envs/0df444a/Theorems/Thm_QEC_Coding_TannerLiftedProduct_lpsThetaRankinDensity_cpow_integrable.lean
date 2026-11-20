-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaRankinDensity_cpow_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_cpow_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:27:51.027091+00:00
-- url     : https://prove2.me/theorems/3dd727bd-3223-4499-a6c1-82684ea3b46b
-- title:
--   Tanner Lifted Product: lps Theta Rankin Density cpow integrable
-- statement:
--   The actual LPS theta square density is integrable against every complex height power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L68-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L68-L71

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_cpow_integrable (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (s : ℂ) :
    IntegrableOn (fun τ : ℍ => (lpsThetaRankinDensity q hq4 τ:ℂ)*(τ.im:ℂ)^s) ModularGroup.fd := by sorry
