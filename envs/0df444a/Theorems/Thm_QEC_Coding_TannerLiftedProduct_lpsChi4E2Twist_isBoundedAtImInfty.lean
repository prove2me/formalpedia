-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_isBoundedAtImInfty
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_isBoundedAtImInfty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:29.677191+00:00
-- url     : https://prove2.me/theorems/a675eddd-1ea3-4637-b349-ca8934181726
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Twist is Bounded At Im Infty
-- statement:
--   The genuine convergent q-series proves boundedness in the full infinity filter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L155-L159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L155-L159

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_isBoundedAtImInfty :
    UpperHalfPlane.IsBoundedAtImInfty (fun z : ℍ => lpsChi4E2Twist z) := by sorry
