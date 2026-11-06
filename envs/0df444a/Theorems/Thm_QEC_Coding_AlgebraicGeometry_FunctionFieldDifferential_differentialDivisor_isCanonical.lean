-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_isCanonical
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_isCanonical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:22:40.947598+00:00
-- url     : https://prove2.me/theorems/4ba3eb39-5360-4bb3-a634-bf8e6548e395
-- title:
--   Function Field Differential: differential Divisor is Canonical
-- statement:
--   The intrinsic divisor of every nonzero differential is canonical.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1056-L1060
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1056-L1060

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

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialDivisor_isCanonical
    (omega : Differential k F) (homega : omega ≠ 0) :
    IsCanonicalDivisor (k := k) (F := F)
      (differentialDivisor (k := k) (F := F) omega homega) := by sorry
