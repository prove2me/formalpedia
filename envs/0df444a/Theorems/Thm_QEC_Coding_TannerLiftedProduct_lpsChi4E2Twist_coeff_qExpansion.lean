-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_coeff_qExpansion
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_coeff_qExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:27.294239+00:00
-- url     : https://prove2.me/theorems/1a4ec44c-f6e1-43cf-a709-2ec4048f9731
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Twist coeff q Expansion
-- statement:
--   Analytic uniqueness identifies every actual twist coefficient with the character-weighted divisor sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L175-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L175-L185

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_coeff_qExpansion (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (fun z : ℍ => lpsChi4E2Twist z)) =
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsChi4E2Character (n:ZMod 4) := by sorry
