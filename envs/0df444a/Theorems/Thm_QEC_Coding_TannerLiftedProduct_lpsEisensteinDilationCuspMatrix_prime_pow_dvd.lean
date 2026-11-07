-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilationCuspMatrix_prime_pow_dvd
-- name    : QEC.Coding.TannerLiftedProduct.lpsEisensteinDilationCuspMatrix_prime_pow_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:03:35.412857+00:00
-- url     : https://prove2.me/theorems/5349df6c-6cb7-485e-8436-bb7d453481fc
-- title:
--   Tanner Lifted Product: lps Eisenstein Dilation Cusp Matrix prime pow dvd
-- statement:
--   A dilation coprime to a modulus preserves every power-divisibility condition on the reduced denominator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L119-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L119-L135

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsEisensteinDilationCuspMatrix_prime_pow_dvd (p m : ℕ) (hm : 0<m)
    (hmp : m.Coprime p) (γ : SL(2,ℤ)) (e : ℕ) :
    (p:ℤ)^e∣γ 1 0 ↔ (p:ℤ)^e∣lpsEisensteinDilationCuspMatrix m hm γ 1 0 := by sorry
