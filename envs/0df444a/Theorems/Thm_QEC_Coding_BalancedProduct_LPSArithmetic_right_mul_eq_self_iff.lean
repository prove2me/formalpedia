-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_right_mul_eq_self_iff
-- name    : QEC.Coding.BalancedProduct.LPSArithmetic.right_mul_eq_self_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:48:44.879246+00:00
-- url     : https://prove2.me/theorems/638460bc-5f85-45ce-a0a9-31aa601be697
-- title:
--   LPSArithmetic: right mul eq self iff
-- statement:
--   Right multiplication by a subgroup element fixes an ambient PGL vertex
--   only for the identity.  This is the vertex-freeness used by the balanced
--   product; edge-freeness additionally requires the LPS quotient condition and
--   is deliberately not asserted here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L116-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L116-L125

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]

theorem QEC.Coding.BalancedProduct.LPSArithmetic.right_mul_eq_self_iff
    (g : PGL(2, R)) (h : upperUnipotentSubgroup (R := R)) :
    g * (h : PGL(2, R)) = g ↔ h = 1 := by sorry
