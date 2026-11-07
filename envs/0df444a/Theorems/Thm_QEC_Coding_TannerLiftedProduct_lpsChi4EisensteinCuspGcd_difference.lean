-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4EisensteinCuspGcd_difference
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4EisensteinCuspGcd_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:50:17.29998+00:00
-- url     : https://prove2.me/theorems/ab577ea5-7021-47ac-9162-7d2a4235699b
-- title:
--   Tanner Lifted Product: lps Chi4 Eisenstein Cusp Gcd difference
-- statement:
--   The two nonzero modulus-four character terms have the exact signed gcd difference at every primitive column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L71-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L71-L102

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsChi4EisensteinCuspGcd_difference (A C : ℤ)
    (hp : ¬(2∣A ∧ 2∣C)) :
    (((Int.gcd (4*A+C) 16:ℕ):ℂ)^2-((Int.gcd (4*A+3*C) 16:ℕ):ℂ)^2)=
      if C%8=4 then -192*lpsChi4E2Character ((A*(C/4):ℤ):ZMod 4) else 0 := by sorry
