-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_divisorDegree_nonnegative_of_mem_nonzero
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.divisorDegree_nonnegative_of_mem_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:21:28.512919+00:00
-- url     : https://prove2.me/theorems/88c5d816-b36c-4134-a2b8-fb936a0eedf6
-- title:
--   Global Place: divisor Degree nonnegative of mem nonzero
-- statement:
--   A divisor with a nonzero Riemann--Roch member has nonnegative weighted
--   degree, because its principal-divisor correction is coefficientwise
--   nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/NegativeDegreeVanishing.lean#L47-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/NegativeDegreeVanishing.lean#L47-L64

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.divisorDegree_nonnegative_of_mem_nonzero
    (G : Divisor (GlobalPlace k F)) {f : F}
    (hmem : f ∈ GlobalPlace.riemannRochSubmodule G) (hf : f ≠ 0) :
    0 ≤ Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G := by sorry
