-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Gauss_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Gauss_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:22.619202+00:00
-- url     : https://prove2.me/theorems/54779fb8-346c-4463-8766-b8aef5ad31a1
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Gauss ne zero
-- statement:
--   The actual nonzero Gauss square validates normalization of the E2 twist.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L67-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L67-L71

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Gauss_ne_zero : gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))≠0 := by sorry
