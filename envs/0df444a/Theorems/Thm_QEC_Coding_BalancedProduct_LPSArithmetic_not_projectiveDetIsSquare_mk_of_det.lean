-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_not_projectiveDetIsSquare_mk_of_det
-- name    : QEC.Coding.BalancedProduct.LPSArithmetic.not_projectiveDetIsSquare_mk_of_det
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:44:33.57377+00:00
-- url     : https://prove2.me/theorems/b30129bd-fe0d-4ff3-a9fd-fad4b22c375d
-- title:
--   LPSArithmetic: not projective Det Is Square mk of det
-- statement:
--   A lift whose determinant is a quadratic nonresidue has nonsquare
--   projective determinant.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L204-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L204-L212

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]

theorem QEC.Coding.BalancedProduct.LPSArithmetic.not_projectiveDetIsSquare_mk_of_det
    {p q : ℕ} [Fact q.Prime]
    (A : GL (Fin 2) (ZMod q))
    (hdet : (A.det : ZMod q) = (p : ZMod q))
    (hq : legendreSym q p = -1) :
    ¬ ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) := by sorry
