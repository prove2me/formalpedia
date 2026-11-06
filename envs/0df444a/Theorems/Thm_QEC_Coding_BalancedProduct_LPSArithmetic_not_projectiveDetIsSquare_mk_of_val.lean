-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_not_projectiveDetIsSquare_mk_of_val
-- name    : QEC.Coding.BalancedProduct.LPSArithmetic.not_projectiveDetIsSquare_mk_of_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:44:36.684795+00:00
-- url     : https://prove2.me/theorems/9853f0aa-afb0-4cf3-b3d0-8961fe5f68cf
-- title:
--   LPSArithmetic: not projective Det Is Square mk of val
-- statement:
--   The LPSArithmetic construction uses the not projective Det Is Square mk of val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L173-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L173-L180

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]

theorem QEC.Coding.BalancedProduct.LPSArithmetic.not_projectiveDetIsSquare_mk_of_val
    (A : GL (Fin 2) R)
    (hA : ¬ IsSquare (A.det : R)) :
    ¬ ProjectiveDetIsSquare (Matrix.ProjGenLinGroup.mk A) := by sorry
