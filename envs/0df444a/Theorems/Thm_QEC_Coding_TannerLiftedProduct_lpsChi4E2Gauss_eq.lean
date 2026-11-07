-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Gauss_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Gauss_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:16.032913+00:00
-- url     : https://prove2.me/theorems/6ce12e68-ad7b-4af4-ab53-57afe1c70626
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Gauss eq
-- statement:
--   The four actual terms evaluate the true Gauss sum as twice the quarter-turn phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L47-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L47-L56

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Gauss_eq : gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))=
    2*ZMod.stdAddChar (1:ZMod 4) := by sorry
