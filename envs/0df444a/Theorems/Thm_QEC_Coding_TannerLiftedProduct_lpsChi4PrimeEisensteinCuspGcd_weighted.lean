-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4PrimeEisensteinCuspGcd_weighted
-- name    : QEC.Coding.TannerLiftedProduct.lpsChi4PrimeEisensteinCuspGcd_weighted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:19:14.479502+00:00
-- url     : https://prove2.me/theorems/85d2443d-eb63-4dfe-b8dc-5278be52b7fb
-- title:
--   Tanner Lifted Product: lps Chi4 Prime Eisenstein Cusp Gcd weighted
-- statement:
--   The actual double-character cusp term factors into its two genuine single-character gcd terms.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L485-L520
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L485-L520

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsChi4PrimeEisensteinCuspGcd_weighted (q : ℕ) [Fact q.Prime] (hq2 : q≠2)
    (γ : SL(2,ℤ)) (r : Fin 4) (a : Fin q) :
    lpsChi4E2Character (r.val:ZMod 4)*lpsQuadraticE2Character q (a.val:ZMod q)*
      ((Int.gcd (((4*q:ℕ):ℤ)*γ 0 0+((q*r.val+4*a.val:ℕ):ℤ)*γ 1 0)
        (((4*q:ℕ):ℤ)*γ 1 0):ℂ)^2/((4*q:ℕ):ℂ)^2)=
      (lpsChi4E2Character (r.val:ZMod 4)*
        ((Int.gcd ((4:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((4:ℤ)*γ 1 0):ℂ)^2/(4:ℂ)^2))*
      (lpsQuadraticE2Character q (a.val:ZMod q)*
        ((Int.gcd ((q:ℤ)*γ 0 0+(a.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2)) := by sorry
