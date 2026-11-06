-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalRelNormCount_relNorm_prime_count_boundary
-- name    : QEC.Coding.AlgebraicGeometry.LocalRelNormCount.relNorm_prime_count_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:28:03.478199+00:00
-- url     : https://prove2.me/theorems/5bdeb5d6-bbee-46fa-979a-4509cd016ff5
-- title:
--   Local Rel Norm Count: rel Norm prime count boundary
-- statement:
--   Direct-chart shape of the missing last step.  Here `e` is the constructed
--   coefficient above, and the intended equality is `e = p.inertiaDeg' P`; proving
--   that equality requires the separable local determinant/length argument in the
--   companion dossier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/LocalRelNormCount.lean#L44-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/LocalRelNormCount.lean#L44-L49

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

theorem QEC.Coding.AlgebraicGeometry.LocalRelNormCount.relNorm_prime_count_boundary
    (P : Ideal S) (p : Ideal R) (hp0 : p ≠ ⊥)
    [P.LiesOver p] [p.IsPrime] :
    Multiset.count p (normalizedFactors (Ideal.relNorm R P)) =
      primeRelNormExponent R S P p := by sorry
