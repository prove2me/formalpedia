-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_projectiveDetIsSquare_conj_iff
-- name    : QEC.Coding.BalancedProduct.LPSArithmetic.projectiveDetIsSquare_conj_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:44:44.91936+00:00
-- url     : https://prove2.me/theorems/5085c2c6-c136-4dd6-bd06-177c2f79132c
-- title:
--   LPSArithmetic: projective Det Is Square conj iff
-- statement:
--   The LPSArithmetic construction uses the projective Det Is Square conj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L276-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L276-L285

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]

theorem QEC.Coding.BalancedProduct.LPSArithmetic.projectiveDetIsSquare_conj_iff
    (g h : PGL(2, R)) :
    ProjectiveDetIsSquare (g * h * g⁻¹) ↔ ProjectiveDetIsSquare h := by sorry
