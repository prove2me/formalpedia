-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_LPSArithmetic_ne_conj_upperUnipotent_of_not_detSquare
-- name    : QEC.Coding.BalancedProduct.LPSArithmetic.ne_conj_upperUnipotent_of_not_detSquare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:53:30.655201+00:00
-- url     : https://prove2.me/theorems/275a99a0-86eb-402c-acd5-3a25a90db921
-- title:
--   LPSArithmetic: ne conj upper Unipotent of not det Square
-- statement:
--   A projective element of nonsquare determinant cannot be conjugate to an
--   upper-unipotent element.  Once the LPS generators are shown to have determinant
--   class `401`, this is exactly the BE20 quotient-condition argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L290-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/LPSArithmetic.lean#L290-L298

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSArithmetic
open Matrix
variable {R : Type*} [CommRing R]

theorem QEC.Coding.BalancedProduct.LPSArithmetic.ne_conj_upperUnipotent_of_not_detSquare
    {s : PGL(2, R)}
    (hs : ¬ ProjectiveDetIsSquare s)
    (g : PGL(2, R)) (x : R) :
    s ≠ g * upperUnipotentPGL x * g⁻¹ := by sorry
