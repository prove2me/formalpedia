-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEisensteinDilationCuspMatrix_column
-- name    : QEC.Coding.TannerLiftedProduct.lpsEisensteinDilationCuspMatrix_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T03:03:12.008823+00:00
-- url     : https://prove2.me/theorems/5ba55494-a046-4d7b-852b-960713ed5124
-- title:
--   Tanner Lifted Product: lps Eisenstein Dilation Cusp Matrix column
-- statement:
--   The constructed determinant-one cusp matrix has the true reduced first column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L38-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCharacterEisensteinDilation.lean#L38-L51

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinDilation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsEisensteinDilationCuspMatrix_column (m : ℕ) (hm : 0<m) (γ : SL(2,ℤ)) :
    (m:ℤ)*γ 0 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 0 0 ∧
      γ 1 0=(Int.gcd (m:ℤ) (γ 1 0):ℤ)*lpsEisensteinDilationCuspMatrix m hm γ 1 0 := by sorry
