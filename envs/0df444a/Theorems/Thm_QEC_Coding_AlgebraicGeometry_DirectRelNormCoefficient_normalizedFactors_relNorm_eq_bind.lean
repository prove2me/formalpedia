-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectRelNormCoefficient_normalizedFactors_relNorm_eq_bind
-- name    : QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.normalizedFactors_relNorm_eq_bind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:18:17.394911+00:00
-- url     : https://prove2.me/theorems/56157abc-9d10-4140-99f4-d3ad29a3f70a
-- title:
--   Direct Rel Norm Coefficient: normalized Factors rel Norm eq bind
-- statement:
--   Relative ideal norm pushes the complete normalized-factor multiset
--   forward by contracting each factor and repeating it by the actual inertia
--   degree.  The proof uses only exact ideal factorization, norm multiplicativity,
--   and the constructed prime norm equation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectRelNormCoefficient.lean#L100-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectRelNormCoefficient.lean#L100-L120

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectNormCount
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_SeparableNormalCover
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_DirectRelNormCoefficient
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient
open scoped BigOperators Polynomial RatFunc nonZeroDivisors
open UniqueFactorizationMonoid
variable (k F : Type*)
variable [Field k] [Finite k] [Field F]
variable [Algebra k[X] F] [Algebra k⟮X⟯ F]
variable [IsScalarTower k[X] k⟮X⟯ F]
variable [_root_.FunctionField k F]
variable [Algebra.IsSeparable k⟮X⟯ F]
local notation3 "R" => k[X]
local notation3 "B" => directRingOfIntegers k F
attribute [local instance] QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.directRelNormCoefficient_isTorsionFree
attribute [local instance] directRelNormCoefficient_isTorsionFree

theorem QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.normalizedFactors_relNorm_eq_bind (I : Ideal B) (hI : I ≠ ⊥) :
    normalizedFactors (Ideal.relNorm R I) =
      (normalizedFactors I).bind fun P =>
        Multiset.replicate ((P.under R).inertiaDeg' P) (P.under R) := by sorry
