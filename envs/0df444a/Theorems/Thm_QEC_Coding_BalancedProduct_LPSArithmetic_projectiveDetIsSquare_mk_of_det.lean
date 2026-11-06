-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_projectiveDetIsSquare_mk_of_det
-- name    : QEC.Coding.BalancedProduct.LPSArithmetic.projectiveDetIsSquare_mk_of_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:49:43.276794+00:00
-- url     : https://prove2.me/theorems/e36a3d7e-7311-4326-9895-b2a55825b9f4
-- title:
--   LPSArithmetic: projective Det Is Square mk of det
-- statement:
--   A lift whose determinant is a quadratic residue has square projective
--   determinant.  This is the elementary determinant-class step used by the
--   `PSL(2,q)` branch of the LPS construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L185-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L185-L200

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]

theorem QEC.Coding.BalancedProduct.LPSArithmetic.projectiveDetIsSquare_mk_of_det
    {p q : ℕ} [Fact q.Prime]
    (A : GL (Fin 2) (ZMod q))
    (hdet : (A.det : ZMod q) = (p : ZMod q))
    (hpq : (p : ZMod q) ≠ 0)
    (hq : legendreSym q p = 1) :
    ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) := by sorry
