-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCuspGcd_weighted_of_dvd
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspGcd_weighted_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:50:05.089688+00:00
-- url     : https://prove2.me/theorems/1dd86f35-4364-4246-b7ac-c504f6a005cd
-- title:
--   Tanner Lifted Product: lps Quadratic Eisenstein Cusp Gcd weighted of dvd
-- statement:
--   The genuine weighted gcd term equals the finite-field root indicator, including the zero residue.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L298-L315
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L298-L315

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspGcd_weighted_of_dvd (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) (D : ℤ) (hC : γ 1 0=(q:ℤ)*D) (r : Fin q) :
    lpsQuadraticE2Character q (r.val:ZMod q)*
      ((Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0):ℂ)^2/(q:ℂ)^2)=
      lpsQuadraticE2Character q (r.val:ZMod q)*
        (if (γ 0 0:ZMod q)+(r.val:ZMod q)*(D:ZMod q)=0 then (q:ℂ)^2 else 1) := by sorry
