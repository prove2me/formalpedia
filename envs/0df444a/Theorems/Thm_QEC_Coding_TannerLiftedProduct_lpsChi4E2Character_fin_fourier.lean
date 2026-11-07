-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_fin_fourier
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Character_fin_fourier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:12:27.526931+00:00
-- url     : https://prove2.me/theorems/d5411582-da41-4b25-b99c-77410597da27
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Character fin fourier
-- statement:
--   Every frequency, including composite-modulus nonunits, has the actual character Fourier transform.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L74-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSChi4Eisenstein.lean#L74-L92

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Character_fin_fourier (n : ZMod 4) :
    (∑ a : Fin 4,lpsChi4E2Character (a.val:ZMod 4)*ZMod.stdAddChar (n*(a.val:ZMod 4)))=
      lpsChi4E2Character n*gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)) := by sorry
