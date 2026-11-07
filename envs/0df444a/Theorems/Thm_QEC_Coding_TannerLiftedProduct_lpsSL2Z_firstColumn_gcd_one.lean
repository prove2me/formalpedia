-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSL2Z_firstColumn_gcd_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_gcd_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:49:49.867888+00:00
-- url     : https://prove2.me/theorems/58c28c66-def5-41d0-bd0d-734b9a4cfee7
-- title:
--   Tanner Lifted Product: lps SL2 Z first Column gcd one
-- statement:
--   Every genuine determinant-one integer matrix has a primitive first column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L38-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinCusps.lean#L38-L47

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsSL2Z_firstColumn_gcd_one (γ : SL(2,ℤ)) : Int.gcd (γ 0 0) (γ 1 0)=1 := by sorry
