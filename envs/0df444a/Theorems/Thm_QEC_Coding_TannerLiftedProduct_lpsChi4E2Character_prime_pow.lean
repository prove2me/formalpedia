-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_prime_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4E2Character_prime_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:36:45.885284+00:00
-- url     : https://prove2.me/theorems/f7f7b3bb-8491-4dce-b4ac-9ab83159a9ac
-- title:
--   Tanner Lifted Product: lps Chi4 E2 Character prime pow
-- statement:
--   Every power of a residue prime congruent to one modulo four has modulus-four character one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L35-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaEisensteinCusps.lean#L35-L40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCorrection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsChi4E2Character_prime_pow (q : ℕ) (hq4 : q%4=1) (b : ℕ) :
    lpsChi4E2Character ((q^b:ℕ):ZMod 4)=1 := by sorry
