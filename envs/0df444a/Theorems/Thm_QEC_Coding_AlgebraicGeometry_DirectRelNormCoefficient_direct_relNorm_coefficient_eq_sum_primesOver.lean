-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectRelNormCoefficient_direct_relNorm_coefficient_eq_sum_primesOver
-- name    : QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.direct_relNorm_coefficient_eq_sum_primesOver
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:43:57.529209+00:00
-- url     : https://prove2.me/theorems/dec4f90e-fad7-447d-a664-9f3a118717ed
-- title:
--   Direct Rel Norm Coefficient: direct rel Norm coefficient eq sum primes Over
-- statement:
--   Direct-chart coefficient identity for every nonzero actual ideal.  This
--   is the factorization form used by the principal specialization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectRelNormCoefficient.lean#L188-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectRelNormCoefficient.lean#L188-L194

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

theorem QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.direct_relNorm_coefficient_eq_sum_primesOver (I : Ideal B) (hI : I ≠ ⊥)
    (p : Ideal R) [p.IsMaximal] (hp0 : p ≠ ⊥) :
    Multiset.count p (normalizedFactors (Ideal.relNorm R I)) =
      ∑ P ∈ IsDedekindDomain.primesOverFinset p B,
        p.inertiaDeg' P * Multiset.count P (normalizedFactors I) := by sorry
