-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_exists_canonicalDivisor
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.exists_canonicalDivisor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:27:22.514071+00:00
-- url     : https://prove2.me/theorems/3a23c4d2-62b8-4755-a88e-1ef791a42da7
-- title:
--   Function Field Differential: exists canonical Divisor
-- statement:
--   A canonical divisor exists, witnessed by the intrinsic divisor of the
--   nonzero function-field differential generator.  This does not define a
--   distinguished global canonical divisor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1065-L1072
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1065-L1072

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

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.exists_canonicalDivisor :
    ∃ K : Divisor (GlobalPlace k F), IsCanonicalDivisor (k := k) (F := F) K := by sorry
