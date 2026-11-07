-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_square
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Character_square
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:54:20.49153+00:00
-- url     : https://prove2.me/theorems/891819ed-9f66-479b-aec0-78731b9c31cf
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Character square
-- statement:
--   The actual modulus-four character takes value one on the square of every unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L577-L582
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L577-L582

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Character_square (d : ZMod 4) (hd : IsUnit d) :
    lpsChi4E2Character (d^2)=1 := by sorry
