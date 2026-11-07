-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntGcd_coprime_mul
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntGcd_coprime_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:51:43.716498+00:00
-- url     : https://prove2.me/theorems/cbabec18-1e1d-4d62-89fa-10c24916d437
-- title:
--   Tanner Lifted Product: lps Int Gcd coprime mul
-- statement:
--   The integer gcd factors over a product of two coprime moduli.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L446-L449
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L446-L449

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsIntGcd_coprime_mul (x N M : ℤ) (hNM : Int.gcd N M=1) :
    Int.gcd x (N*M)=Int.gcd x N*Int.gcd x M := by sorry
