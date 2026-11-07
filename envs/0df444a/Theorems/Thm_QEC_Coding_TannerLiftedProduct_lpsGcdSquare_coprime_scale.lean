-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGcdSquare_coprime_scale
-- name    : QEC.Coding.TannerLiftedProduct.lpsGcdSquare_coprime_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:51:18.890207+00:00
-- url     : https://prove2.me/theorems/4129b6cf-dad5-4c14-bbff-94946f2f5ec8
-- title:
--   Tanner Lifted Product: lps Gcd Square coprime scale
-- statement:
--   A coprime scale and the corresponding translated column preserve the gcd with the squared modulus.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L414-L443
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L414-L443

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsGcdSquare_coprime_scale (N M A C r s : ℤ)
    (hM : Int.gcd M N=1) (hr : Int.gcd r N=1) :
    Int.gcd (M*N*A+(M*r+N*s)*C) (N^2)=Int.gcd (N*A+r*C) (N^2) := by sorry
