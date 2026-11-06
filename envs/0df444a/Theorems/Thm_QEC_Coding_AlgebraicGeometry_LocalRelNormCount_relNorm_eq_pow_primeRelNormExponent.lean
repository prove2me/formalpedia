-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalRelNormCount_relNorm_eq_pow_primeRelNormExponent
-- name    : QEC.Coding.AlgebraicGeometry.LocalRelNormCount.relNorm_eq_pow_primeRelNormExponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:42:52.567882+00:00
-- url     : https://prove2.me/theorems/e4c724c1-56dc-4ec8-bb46-cebb26643041
-- title:
--   Local Rel Norm Count: rel Norm eq pow prime Rel Norm Exponent
-- statement:
--   The constructed exponent has its defining relative-norm equality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/LocalRelNormCount.lean#L21-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/LocalRelNormCount.lean#L21-L24

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

theorem QEC.Coding.AlgebraicGeometry.LocalRelNormCount.relNorm_eq_pow_primeRelNormExponent (P : Ideal S) (p : Ideal R)
    [P.LiesOver p] [p.IsPrime] :
    Ideal.relNorm R P = p ^ primeRelNormExponent R S P p := by sorry
