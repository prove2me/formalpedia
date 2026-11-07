-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilation_weightedCuspGcd
-- name    : QEC.Coding.TannerLiftedProduct.lpsEisensteinDilation_weightedCuspGcd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:03:14.043554+00:00
-- url     : https://prove2.me/theorems/346c69b4-b5a2-4615-87a5-8265f26188ed
-- title:
--   Tanner Lifted Product: lps Eisenstein Dilation weighted Cusp Gcd
-- statement:
--   Every actual finite weighted gcd vector retains its precise dilation scaling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L70-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L70-L83

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsEisensteinDilation_weightedCuspGcd (N m : ℕ) (hm : 0<m)
    (γ : SL(2,ℤ)) (w : Fin N→ℂ) :
    (∑ r : Fin N,w r*((Int.gcd ((N:ℤ)*(m:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
      ((N:ℤ)*γ 1 0):ℂ)^2/((N:ℂ)^2*(m:ℂ)^2)))=
      ((Int.gcd (m:ℤ) (γ 1 0):ℂ)^2/(m:ℂ)^2)*
        (∑ r : Fin N,w r*((Int.gcd ((N:ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 0 0+
          (r.val:ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 1 0)
          ((N:ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 1 0):ℂ)^2/(N:ℂ)^2)) := by sorry
