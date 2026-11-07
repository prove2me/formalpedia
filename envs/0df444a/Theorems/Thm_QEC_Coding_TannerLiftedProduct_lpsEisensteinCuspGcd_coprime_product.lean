-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinCuspGcd_coprime_product
-- name    : QEC.Coding.TannerLiftedProduct.lpsEisensteinCuspGcd_coprime_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:51:49.681566+00:00
-- url     : https://prove2.me/theorems/91f54f15-ac9f-436e-898d-411446db266f
-- title:
--   Tanner Lifted Product: lps Eisenstein Cusp Gcd coprime product
-- statement:
--   The actual primitive-column cusp gcd factors over coprime moduli and their CRT translation residues.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L452-L482
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L452-L482

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsEisensteinCuspGcd_coprime_product (N M : ℤ) (γ : SL(2,ℤ)) (r s : ℤ)
    (hNM : Int.gcd N M=1) (hr : Int.gcd r N=1) (hs : Int.gcd s M=1) :
    Int.gcd ((N*M)*γ 0 0+(M*r+N*s)*γ 1 0) ((N*M)*γ 1 0)=
      Int.gcd (N*γ 0 0+r*γ 1 0) (N*γ 1 0)*
        Int.gcd (M*γ 0 0+s*γ 1 0) (M*γ 1 0) := by sorry
