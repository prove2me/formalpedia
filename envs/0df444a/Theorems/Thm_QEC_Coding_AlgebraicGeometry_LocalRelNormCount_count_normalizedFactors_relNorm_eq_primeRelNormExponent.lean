-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalRelNormCount_count_normalizedFactors_relNorm_eq_primeRelNormExponent
-- name    : QEC.Coding.AlgebraicGeometry.LocalRelNormCount.count_normalizedFactors_relNorm_eq_primeRelNormExponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:42:57.9389+00:00
-- url     : https://prove2.me/theorems/eb4aaa35-6e37-422b-bbf6-d22fb5052ff7
-- title:
--   Local Rel Norm Count: count normalized Factors rel Norm eq prime Rel Norm Exponent
-- statement:
--   The local exponent is exactly the normalized-factor coefficient of the
--   actual relative ideal norm at the lower prime.  This reduces the desired
--   principal norm count formula to identifying this existing exponent with the
--   actual inertia degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/LocalRelNormCount.lean#L30-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/LocalRelNormCount.lean#L30-L38

import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_LocalRelNormCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.LocalRelNormCount
open UniqueFactorizationMonoid
variable (R S : Type*)
variable [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain R]
variable [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [IsDedekindDomain S]
variable [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

theorem QEC.Coding.AlgebraicGeometry.LocalRelNormCount.count_normalizedFactors_relNorm_eq_primeRelNormExponent
    (P : Ideal S) (p : Ideal R) (hp0 : p ≠ ⊥)
    [P.LiesOver p] [p.IsPrime] :
    Multiset.count p (normalizedFactors (Ideal.relNorm R P)) =
      primeRelNormExponent R S P p := by sorry
