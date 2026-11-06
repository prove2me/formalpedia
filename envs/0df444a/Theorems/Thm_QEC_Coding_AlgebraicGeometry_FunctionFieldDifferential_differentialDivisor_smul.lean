-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_smul
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:25:31.974579+00:00
-- url     : https://prove2.me/theorems/66a536f1-7764-4e4f-8e51-e55c6ff2b5be
-- title:
--   Function Field Differential: differential Divisor smul
-- statement:
--   Scaling a chosen nonzero differential by a nonzero function changes its
--   differential divisor by the corresponding principal divisor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1030-L1046
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1030-L1046

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_smul
    [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    (u : Fˣ) (omega : Differential k F) (homega : omega ≠ 0) :
    differentialDivisor (k := k) (F := F) ((u : F) • omega)
        (smul_ne_zero u.ne_zero homega) =
      GlobalPlace.principalDivisor (k := k) (F := F) u +
        differentialDivisor (k := k) (F := F) omega homega := by sorry
