-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaRankinDensity_exp_decay
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_exp_decay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:27:32.800668+00:00
-- url     : https://prove2.me/theorems/5fb6b3b9-e28e-4514-ab70-842e3e92b0cf
-- title:
--   Tanner Lifted Product: lps Theta Rankin Density exp decay
-- statement:
--   The actual LPS theta square density decays exponentially at infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L50-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L50-L53

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_exp_decay (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    ∃a>0,lpsThetaRankinDensity q hq4=O[atImInfty] (fun τ => Real.exp (-a*τ.im)) := by sorry
