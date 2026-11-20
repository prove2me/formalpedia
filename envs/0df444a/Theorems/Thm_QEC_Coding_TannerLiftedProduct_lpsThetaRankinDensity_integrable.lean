-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaRankinDensity_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:28:29.868385+00:00
-- url     : https://prove2.me/theorems/faceedb8-b8be-4da0-876e-0d9511fd0763
-- title:
--   Tanner Lifted Product: lps Theta Rankin Density integrable
-- statement:
--   The actual LPS theta square density has a convergent hyperbolic integral.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L56-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L56-L59

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_integrable (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    IntegrableOn (lpsThetaRankinDensity q hq4) ModularGroup.fd := by sorry
