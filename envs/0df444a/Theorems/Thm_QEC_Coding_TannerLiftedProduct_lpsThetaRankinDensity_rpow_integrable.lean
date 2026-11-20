-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaRankinDensity_rpow_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_rpow_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:28:22.475187+00:00
-- url     : https://prove2.me/theorems/4517c497-3d13-4e86-9638-d3e3dea64ac3
-- title:
--   Tanner Lifted Product: lps Theta Rankin Density rpow integrable
-- statement:
--   The actual LPS theta square density is integrable against every real height power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L62-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L62-L65

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_rpow_integrable (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (s : ℝ) :
    IntegrableOn (fun τ : ℍ => lpsThetaRankinDensity q hq4 τ*τ.im^s) ModularGroup.fd := by sorry
