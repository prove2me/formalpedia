-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochSubmodule_eq_bot_of_negative_degree
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule_eq_bot_of_negative_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:21:30.26981+00:00
-- url     : https://prove2.me/theorems/ea74762a-a0b4-489e-887d-7720186e646d
-- title:
--   Global Place: riemann Roch Submodule eq bot of negative degree
-- statement:
--   A divisor of negative constructed degree has only zero in its actual
--   all-place Riemann--Roch submodule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/NegativeDegreeVanishing.lean#L68-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/NegativeDegreeVanishing.lean#L68-L79

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochSubmodule_eq_bot_of_negative_degree
    (G : Divisor (GlobalPlace k F))
    (hdegree : Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) G < 0) :
    GlobalPlace.riemannRochSubmodule G = ⊥ := by sorry
