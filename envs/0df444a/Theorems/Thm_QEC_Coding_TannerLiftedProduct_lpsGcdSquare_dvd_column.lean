-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGcdSquare_dvd_column
-- name    : QEC.Coding.TannerLiftedProduct.lpsGcdSquare_dvd_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:51:29.707988+00:00
-- url     : https://prove2.me/theorems/27ce5c38-7711-4b0f-97b3-35c31725169a
-- title:
--   Tanner Lifted Product: lps Gcd Square dvd column
-- statement:
--   A unit translation residue makes the gcd with the squared modulus divide the scaled denominator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L397-L411
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L397-L411

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsGcdSquare_dvd_column (N A C r : ℤ) (hr : Int.gcd r (N^2)=1) :
    (Int.gcd (N*A+r*C) (N^2):ℤ)∣N*C := by sorry
