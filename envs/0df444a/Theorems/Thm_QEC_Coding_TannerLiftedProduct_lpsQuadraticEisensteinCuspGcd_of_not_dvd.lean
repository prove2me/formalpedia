-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCuspGcd_of_not_dvd
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspGcd_of_not_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:50:39.477271+00:00
-- url     : https://prove2.me/theorems/07be6cba-98b5-4f7f-9514-103713adf315
-- title:
--   Tanner Lifted Product: lps Quadratic Eisenstein Cusp Gcd of not dvd
-- statement:
--   If the residue prime does not divide the cusp denominator every unit-shift gcd is one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L222-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L222-L245

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspGcd_of_not_dvd (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) (r : Fin q) (hr : r≠0) (hC : ¬(q:ℤ)∣γ 1 0) :
    Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0)=1 := by sorry
