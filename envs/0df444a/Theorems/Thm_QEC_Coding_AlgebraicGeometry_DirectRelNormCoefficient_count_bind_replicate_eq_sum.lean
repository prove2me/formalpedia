-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_DirectRelNormCoefficient_count_bind_replicate_eq_sum
-- name    : QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.count_bind_replicate_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:45:36.517514+00:00
-- url     : https://prove2.me/theorems/45563e77-9c7a-4bf5-a788-10cb570f1af0
-- title:
--   Direct Rel Norm Coefficient: count bind replicate eq sum
-- statement:
--   Count a target after replacing every source occurrence by a finite block
--   of repeated target occurrences.  This is the reusable finite collection step
--   for any weighted pushforward of a normalized-factor multiset.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectRelNormCoefficient.lean#L21-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Divisors/DirectRelNormCoefficient.lean#L21-L29

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
variable {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]

theorem QEC.Coding.AlgebraicGeometry.DirectRelNormCoefficient.count_bind_replicate_eq_sum (s : Multiset alpha) (f : alpha → beta)
    (w : alpha → Nat) (q : beta) :
    Multiset.count q (s.bind fun a => Multiset.replicate (w a) (f a)) =
      ∑ a ∈ s.toFinset, (if f a = q then w a else 0) * s.count a := by sorry
