-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDilationColumnGcdDvd
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDilationColumnGcdDvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:08:33.322684+00:00
-- url     : https://prove2.me/theorems/0a626c31-6a5b-4f93-9606-e1aa5e52601b
-- title:
--   Tanner Lifted Product: lps Original Dilation Column Gcd Dvd
-- statement:
--   The actual first-column gcd divides the level by the genuine integral determinant identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L100-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L100-L110

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDilationColumnGcdDvd (N : ℕ) (γ : SL(2,ℤ)) :
    Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0)∣N := by sorry
