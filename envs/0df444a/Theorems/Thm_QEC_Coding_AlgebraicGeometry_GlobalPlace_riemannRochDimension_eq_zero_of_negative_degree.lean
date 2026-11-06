-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_eq_zero_of_negative_degree
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_eq_zero_of_negative_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:22:42.785658+00:00
-- url     : https://prove2.me/theorems/62936a4f-e97a-4bd5-9320-bbc2689d0d07
-- title:
--   Global Place: riemann Roch Dimension eq zero of negative degree
-- statement:
--   The Riemann--Roch dimension is zero for a divisor of negative degree.
--
--   This is the final clause of the source-facing Riemann--Roch statement.  It is
--   proved from the constructed principal-divisor product formula and the actual
--   valuation-bound submodule, not from a supplied Riemann--Roch theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Dimension.lean#L48-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Dimension.lean#L48-L55

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_NegativeDegreeVanishing
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_FiniteDimensional
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Dimension
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_eq_zero_of_negative_degree
    (G : Divisor (GlobalPlace k F))
    [FiniteDimensional k (riemannRochSubmodule G)]
    (hdegree : Divisor.degree (residueDegree (k := k) (F := F)) G < 0) :
    riemannRochDimension G = 0 := by sorry
