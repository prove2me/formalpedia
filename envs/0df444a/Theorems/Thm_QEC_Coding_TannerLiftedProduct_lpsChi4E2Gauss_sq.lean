-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Gauss_sq
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Gauss_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:31.30112+00:00
-- url     : https://prove2.me/theorems/e0e6d7ec-a958-4369-8c5e-afa2fe61e6e9
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Gauss sq
-- statement:
--   The genuine phase square proves Gauss square minus four, without an assumed normalization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L59-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L59-L64

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Gauss_sq : gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))^2= -4 := by sorry
