-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:27.214385+00:00
-- url     : https://prove2.me/theorems/b097acd2-ec64-4935-9ccd-cc3f0f8619d3
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Twist has Sum
-- statement:
--   The genuine translated E2 series and full finite Fourier transform compute the convergent twist series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L104-L136
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L104-L136

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_hasSum (z : ℍ) :
    HasSum (fun n : ℕ => -24*(ArithmeticFunction.sigma 1 n:ℂ) *
      lpsChi4E2Character (n:ZMod 4) * Function.Periodic.qParam 1 (z:ℂ)^n)
      (lpsChi4E2Twist z) := by sorry
