-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_qExpansion_lpsChi4E2TwistModularForm
-- name    : QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsChi4E2TwistModularForm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:28.467265+00:00
-- url     : https://prove2.me/theorems/c3e6cdd3-2e25-4d0d-bc30-684a0c02d728
-- title:
--   Tanner Lifted Product: coeff q Expansion lps Chi4 E2 Twist Modular Form
-- statement:
--   The actual modular form retains every proved character-weighted divisor coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L316-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L316-L319

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.coeff_qExpansion_lpsChi4E2TwistModularForm (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 lpsChi4E2TwistModularForm)=
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsChi4E2Character (n:ZMod 4) := by sorry
