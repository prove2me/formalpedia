-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticEisensteinCuspGcd_of_dvd
-- name    : QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspGcd_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:50:46.855278+00:00
-- url     : https://prove2.me/theorems/586e7d43-13b7-4da1-ae61-6c8d32ebc95d
-- title:
--   Tanner Lifted Product: lps Quadratic Eisenstein Cusp Gcd of dvd
-- statement:
--   A denominator divisible by the residue prime yields the exact unique-root gcd classification.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L277-L295
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L277-L295

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsQuadraticEisensteinCuspGcd_of_dvd (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) (r : Fin q) (hr : r≠0) (D : ℤ) (hC : γ 1 0=(q:ℤ)*D) :
    Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0) ((q:ℤ)*γ 1 0)=
      if (((γ 0 0+(r.val:ℤ)*D):ℤ):ZMod q)=0 then q^2 else q := by sorry
