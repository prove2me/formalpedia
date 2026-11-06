-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_not_projectiveDetIsSquare_mk_of_det_401
-- name    : QEC.Coding.BalancedProduct.LPSArithmetic.not_projectiveDetIsSquare_mk_of_det_401
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:51:29.989885+00:00
-- url     : https://prove2.me/theorems/b2561fe3-0e9f-46ef-846f-78bca192e7b2
-- title:
--   LPSArithmetic: not projective Det Is Square mk of det 401
-- statement:
--   The exact determinant calculation needed for the BE20 choice `p = 401`:
--   an LPS lift with determinant `401` has nonsquare projective determinant at
--   every admissible prime `q`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L257-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L257-L263

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]

theorem QEC.Coding.BalancedProduct.LPSArithmetic.not_projectiveDetIsSquare_mk_of_det_401
    {q : ℕ} [Fact q.Prime]
    (A : GL (Fin 2) (ZMod q))
    (hdet : (A.det : ZMod q) = (401 : ZMod q))
    (hq : legendreSym q 401 = -1) :
    ¬ ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) := by sorry
