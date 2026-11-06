-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_add_coefficient_nonnegative_of_mem
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.order_add_coefficient_nonnegative_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:21:37.758711+00:00
-- url     : https://prove2.me/theorems/011ffe78-8dc3-47d7-83fa-dde68d697126
-- title:
--   Global Place: order add coefficient nonnegative of mem
-- statement:
--   A nonzero Riemann--Roch member gives the coefficientwise nonnegative
--   divisor required by the degree argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/NegativeDegreeVanishing.lean#L32-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/NegativeDegreeVanishing.lean#L32-L42

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Space
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
variable [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.order_add_coefficient_nonnegative_of_mem
    (G : Divisor (GlobalPlace k F)) {f : F}
    (hmem : f ∈ GlobalPlace.riemannRochSubmodule G) (hf : f ≠ 0)
    (P : GlobalPlace k F) :
    0 ≤ GlobalPlace.order P f + G P := by sorry
