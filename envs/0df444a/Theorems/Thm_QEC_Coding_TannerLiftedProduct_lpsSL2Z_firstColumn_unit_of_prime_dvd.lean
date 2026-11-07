-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSL2Z_firstColumn_unit_of_prime_dvd
-- name    : QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_unit_of_prime_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:51:06.65234+00:00
-- url     : https://prove2.me/theorems/898f6479-d872-472e-8628-9865e9da98c3
-- title:
--   Tanner Lifted Product: lps SL2 Z first Column unit of prime dvd
-- statement:
--   Primitivity makes the numerator a prime-modulus unit when the prime divides the denominator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L339-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L339-L345

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_unit_of_prime_dvd (q : ℕ) [Fact q.Prime]
    (γ : SL(2,ℤ)) (hC : (q:ℤ)∣γ 1 0) : (γ 0 0:ZMod q)≠0 := by sorry
