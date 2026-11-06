-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_principal_add
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_principal_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:25:22.699146+00:00
-- url     : https://prove2.me/theorems/272eff64-684d-46eb-9adc-db9302bcc439
-- title:
--   Global Place: riemann Roch Dimension principal add
-- statement:
--   The finite-dimensional Riemann--Roch dimension is invariant when the
--   divisor is shifted by an actual principal divisor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PrincipalShift.lean#L118-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/PrincipalShift.lean#L118-L129

import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Dimension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc WithZero
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k F : Type*}
variable [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.riemannRochDimension_principal_add
    (u : Fˣ) (G : Divisor (GlobalPlace k F))
    [FiniteDimensional k
      (riemannRochSubmodule
        (GlobalPlace.principalDivisor (k := k) (F := F) u + G))]
    [FiniteDimensional k (riemannRochSubmodule G)] :
    riemannRochDimension
        (GlobalPlace.principalDivisor (k := k) (F := F) u + G) =
      riemannRochDimension G := by sorry
