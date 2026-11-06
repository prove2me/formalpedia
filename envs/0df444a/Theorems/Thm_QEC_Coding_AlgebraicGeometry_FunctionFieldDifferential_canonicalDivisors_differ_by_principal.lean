-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_canonicalDivisors_differ_by_principal
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.canonicalDivisors_differ_by_principal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:23:42.01036+00:00
-- url     : https://prove2.me/theorems/979e7bcb-22fd-4c5a-bc54-503585d2ccbd
-- title:
--   Function Field Differential: canonical Divisors differ by principal
-- statement:
--   Any two canonical divisors differ by a principal divisor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1075-L1102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1075-L1102

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

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.canonicalDivisors_differ_by_principal
    [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    {K L : Divisor (GlobalPlace k F)}
    (hK : IsCanonicalDivisor (k := k) (F := F) K)
    (hL : IsCanonicalDivisor (k := k) (F := F) L) :
    ∃ u : Fˣ, L = GlobalPlace.principalDivisor (k := k) (F := F) u + K := by sorry
