-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_projectiveDetIsSquare_iff_mem_range_toPGL
-- name    : QEC.Coding.BalancedProduct.LPSArithmetic.projectiveDetIsSquare_iff_mem_range_toPGL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:51:31.653894+00:00
-- url     : https://prove2.me/theorems/3435fab5-288a-4d33-944e-f86243d8ee2a
-- title:
--   LPSArithmetic: projective Det Is Square iff mem range to PGL
-- statement:
--   In rank two, the image of `PSL(2,R)` inside `PGL(2,R)` is exactly the
--   square-determinant class.  The forward direction rescales a square-determinant
--   lift to determinant one; the reverse direction uses the determinant-one
--   representative of a projective special-linear element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L218-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L218-L252

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]

theorem QEC.Coding.BalancedProduct.LPSArithmetic.projectiveDetIsSquare_iff_mem_range_toPGL
    (g : PGL(2, R)) :
    ProjectiveDetIsSquare g ↔
      g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := R)).range := by sorry
