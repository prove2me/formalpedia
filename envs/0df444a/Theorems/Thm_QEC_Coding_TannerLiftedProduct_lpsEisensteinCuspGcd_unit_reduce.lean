-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinCuspGcd_unit_reduce
-- name    : QEC.Coding.TannerLiftedProduct.lpsEisensteinCuspGcd_unit_reduce
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:49:21.313196+00:00
-- url     : https://prove2.me/theorems/e1307a84-d622-4e50-a994-69e6fdd96086
-- title:
--   Tanner Lifted Product: lps Eisenstein Cusp Gcd unit reduce
-- statement:
--   For a unit translation residue the actual cusp gcd reduces to the fixed squared modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L50-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L50-L68

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsEisensteinCuspGcd_unit_reduce (N : ℤ) (γ : SL(2,ℤ)) (r : ℤ)
    (hr : r.natAbs.Coprime (N.natAbs^2)) :
    Int.gcd (N*γ 0 0+r*γ 1 0) (N*γ 1 0)=
      Int.gcd (N*γ 0 0+r*γ 1 0) (N^2) := by sorry
