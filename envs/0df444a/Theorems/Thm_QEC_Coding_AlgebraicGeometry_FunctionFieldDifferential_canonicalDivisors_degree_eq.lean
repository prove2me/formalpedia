-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_canonicalDivisors_degree_eq
-- name    : QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.canonicalDivisors_degree_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:27:51.766594+00:00
-- url     : https://prove2.me/theorems/0c47c12c-f6e3-4aa1-b1e3-2b9c6bf3abd5
-- title:
--   Function Field Differential: canonical Divisors degree eq
-- statement:
--   The Function Field Differential construction uses the canonical Divisors degree eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1104-L1113
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/CanonicalDifferential.lean#L1104-L1113

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

theorem QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.canonicalDivisors_degree_eq
    [π : Algebra (Polynomial k) F]
    [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
    {K L : Divisor (GlobalPlace k F)}
    (hK : IsCanonicalDivisor (k := k) (F := F) K)
    (hL : IsCanonicalDivisor (k := k) (F := F) L) :
    Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) K =
      Divisor.degree (GlobalPlace.residueDegree (k := k) (F := F)) L := by sorry
