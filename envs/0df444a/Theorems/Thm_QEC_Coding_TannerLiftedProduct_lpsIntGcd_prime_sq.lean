-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntGcd_prime_sq
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntGcd_prime_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:50:32.167071+00:00
-- url     : https://prove2.me/theorems/f3d5ed11-462d-4e69-9b8b-aa115571287e
-- title:
--   Tanner Lifted Product: lps Int Gcd prime sq
-- statement:
--   The gcd with a prime squared is classified by its two actual divisibility tests.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L105-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L105-L129

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsIntGcd_prime_sq (q : ℕ) [Fact q.Prime] (x : ℤ) :
    Int.gcd x ((q:ℤ)^2)=
      if (q:ℤ)^2∣x then q^2 else if (q:ℤ)∣x then q else 1 := by sorry
