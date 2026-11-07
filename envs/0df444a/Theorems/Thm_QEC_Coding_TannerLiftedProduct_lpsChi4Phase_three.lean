-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4Phase_three
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4Phase_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:28.433114+00:00
-- url     : https://prove2.me/theorems/6156ba5e-105c-4205-a604-179517c5f8d8
-- title:
--   Tanner Lifted Product: lps Chi4 Phase three
-- statement:
--   The genuine standard character at three is minus its value at one, used by Gauss and Fourier evaluation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L42-L44
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L42-L44

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4Phase_three : ZMod.stdAddChar (3:ZMod 4)= -ZMod.stdAddChar (1:ZMod 4) := by sorry
