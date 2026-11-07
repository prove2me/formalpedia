-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_tendsto_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_tendsto_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:16:47.178785+00:00
-- url     : https://prove2.me/theorems/b0dc6f91-2457-4f3c-bc8c-1e539652ff13
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Twist tendsto zero
-- statement:
--   The actual zero coefficient and analytic cusp function prove vanishing at infinity in the full filter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L323-L337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L323-L337

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_tendsto_zero :
    Tendsto (lpsChi4E2Twist) UpperHalfPlane.atImInfty (𝓝 0) := by sorry
