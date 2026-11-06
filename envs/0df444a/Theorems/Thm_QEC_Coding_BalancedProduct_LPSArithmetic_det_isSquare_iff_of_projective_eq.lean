-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_det_isSquare_iff_of_projective_eq
-- name    : QEC.Coding.BalancedProduct.LPSArithmetic.det_isSquare_iff_of_projective_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:44:26.185562+00:00
-- url     : https://prove2.me/theorems/eb7d919a-8955-4d1b-8591-680fb5348f9f
-- title:
--   LPSArithmetic: det is Square iff of projective eq
-- statement:
--   Equality in `PGL(2, R)` preserves whether the determinant of a lift is a
--   square.  This is the rank-two reason the determinant square class descends to
--   the projective quotient: changing a lift multiplies its determinant by the
--   square of a scalar unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L133-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L133-L157

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]

theorem QEC.Coding.BalancedProduct.LPSArithmetic.det_isSquare_iff_of_projective_eq
    {A B : GL (Fin 2) R}
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    IsSquare A.det ↔ IsSquare B.det := by sorry
