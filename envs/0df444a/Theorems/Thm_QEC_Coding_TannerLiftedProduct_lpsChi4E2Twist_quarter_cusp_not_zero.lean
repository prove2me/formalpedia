-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_quarter_cusp_not_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_quarter_cusp_not_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:43.35335+00:00
-- url     : https://prove2.me/theorems/fca7747a-05c3-4382-a101-50107a1c5dc7
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Twist quarter cusp not zero
-- statement:
--   The genuine nonzero Gauss normalization rejects vanishing at the quarter cusp.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L357-L361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L357-L361

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_quarter_cusp_not_zero :
    ¬UpperHalfPlane.IsZeroAtImInfty (lpsChi4E2Twist ∣[(2:ℤ)] lpsE2PrimeCuspMatrix 4) := by sorry
