-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_degree_zero
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_degree_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:19:12.907203+00:00
-- url     : https://prove2.me/theorems/4787936c-7927-41a7-82ac-bda09709876a
-- title:
--   Global Place: principal Divisor degree zero
-- statement:
--   The weighted degree of the finite-support all-place principal divisor is
--   zero.  Its direct and inverse chart contributions are computed from actual
--   Dedekind factorization and the finite inverse fibre, then cancel at the
--   rational-base infinity place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/GlobalPrincipalDegree.lean#L40-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/GlobalPrincipalDegree.lean#L40-L49

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

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.principalDivisor_degree_zero (f : Fˣ) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F))
      (GlobalPlace.principalDivisor (k := k) (F := F) f) = 0 := by sorry
