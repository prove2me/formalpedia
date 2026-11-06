-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalOrder_weighted_sum_eq_zero
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.principalOrder_weighted_sum_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:19:17.348209+00:00
-- url     : https://prove2.me/theorems/2c05451b-f5e9-4da6-a0c4-b944814a34f7
-- title:
--   Global Place: principal Order weighted sum eq zero
-- statement:
--   The same product formula, displayed as the finite weighted support sum
--   consumed by divisor calculations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/GlobalPrincipalDegree.lean#L53-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/GlobalPrincipalDegree.lean#L53-L57

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_InverseFibrePrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_RationalBaseInfinityCancellation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped Polynomial RatFunc
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
variable [Algebra k F]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.principalOrder_weighted_sum_eq_zero (f : Fˣ) :
    (GlobalPlace.principalDivisor (k := k) (F := F) f).sum
        (fun P coefficient => coefficient *
          (GlobalPlace.residueDegree (k := k) (F := F) P : Int)) = 0 := by sorry
