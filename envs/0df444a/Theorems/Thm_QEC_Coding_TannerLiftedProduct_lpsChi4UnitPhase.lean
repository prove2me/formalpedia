-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4UnitPhase
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4UnitPhase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:35:53.438524+00:00
-- url     : https://prove2.me/theorems/491af37a-e460-46b7-a6ea-19f1920e5998
-- title:
--   Tanner Lifted Product: lps Chi4 Unit Phase
-- statement:
--   The primitive modulus-four additive phase at a unit is the actual Gauss sum times its character.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L183-L196
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspLocalFactors.lean#L183-L196

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsChi4UnitPhase (d : ZMod 4) (hd : IsUnit d) :
    2*ZMod.stdAddChar d=gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*lpsChi4E2Character d := by sorry
