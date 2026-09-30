-- Prove2me | Theorems.Thm_TauCeti_GlobalNumberFields_Modulus_isCoprimeTo_of_dvd_span_singleton
-- name    : TauCeti.GlobalNumberFields.Modulus.isCoprimeTo_of_dvd_span_singleton
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:41:11.895346+00:00
-- url     : https://prove2.me/theorems/088a6d1e-27d1-4c88-b14e-3a4440129807
-- title:
--   Coprimality of a divisor of a principal ideal
-- statement:
--   Let $K$ be a number field and $\mathfrak m=(\mathfrak m_0,\mathfrak m_\infty)$ a modulus, with nonzero integral ideal $\mathfrak m_0$ and a finite set $\mathfrak m_\infty$ of real places. Let $a\in\mathcal O_K$ be nonzero, and suppose $a$ is a local unit at every prime dividing $\mathfrak m_0$. For every integral ideal $J$ dividing the principal ideal $(a)$,
--
--   $$
--   J+\mathfrak m_0=\mathcal O_K.
--   $$
--
--   This passes a coprimality condition on a principal generator to each ideal divisor of its principal ideal.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Modulus.lean#L489-L504) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Modulus.lean#L489-L504

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Moduli of a number field and multiplicative congruence

A **modulus** of a number field `K` is a pair consisting of a nonzero integral ideal of `𝓞 K` (the
finite part) and a finite set of real infinite places (the infinite part).  Moduli are the data
against which the congruence conditions defining ray classes are imposed: an element `x` of `Kˣ` is
*congruent to one modulo `𝔪`* when the finite part divides `x - 1` locally at each of its prime
divisors, and `x` is positive at each real place selected by the infinite part.

This file builds that vocabulary:

* the carrier `Modulus K`, its divisibility relation, its finite support and exponent function, the
  trivial modulus and the modulus with unit finite part and every real place;
* the predicate `IsCongrOne` and the subgroup `congruenceSubgroup` of `Kˣ` it cuts out, together
  with the larger subgroup `primeToSubgroup` of elements that are units at the primes dividing the
  finite part, and the subgroup `unitsCongruenceSubgroup` of `(𝓞 K)ˣ` obtained by restriction;
* the group `idealsPrimeTo 𝔪` of invertible fractional ideals and the monoid
  `integralIdealsPrimeTo 𝔪` of nonzero integral ideals that are prime to the finite part.

The last two are *abbreviations* for `TauCeti.NumberFieldArithmetic.idealsAway 𝔪.support` and
`TauCeti.NumberFieldArithmetic.integralIdealsAway 𝔪.support`: there is exactly one group of
prime-to fractional ideals and one monoid of prime-to integral ideals, and both are the ones built
away from a finite set of primes.

## Main definitions

* `TauCeti.GlobalNumberFields.Modulus`: the carrier, with `Modulus.support`, `Modulus.exponent`,
  `Modulus.one` and `TauCeti.GlobalNumberFields.narrowModulus`.
* `TauCeti.GlobalNumberFields.IsCongrOne`: multiplicative congruence to one modulo a modulus.
* `TauCeti.GlobalNumberFields.congruenceSubgroup`, `TauCeti.GlobalNumberFields.primeToSubgroup`,
  `TauCeti.GlobalNumberFields.unitsCongruenceSubgroup`: the subgroups of `Kˣ` and `(𝓞 K)ˣ` these
  conditions define.
* `TauCeti.GlobalNumberFields.unitsToPrimeToSubgroup`: the inclusion of `(𝓞 K)ˣ` into
  `primeToSubgroup 𝔪`.
* `TauCeti.GlobalNumberFields.idealsPrimeTo`,
  `TauCeti.GlobalNumberFields.integralIdealsPrimeTo`: ideals prime to the finite part, with the
  inclusion `TauCeti.GlobalNumberFields.integralIdealsPrimeToInclusion` along divisibility.

## Main results

* `TauCeti.GlobalNumberFields.Modulus.mem_support_iff`: membership in the support is divisibility
  of the finite part.  `Modulus.support_one` and `Modulus.support_mono` are consequences.
* `TauCeti.GlobalNumberFields.Modulus.pow_exponent_dvd_finitePart` and
  `TauCeti.GlobalNumberFields.Modulus.mem_finitePart_of_forall_mem_pow_exponent`: the prime power
  prescribed by the exponent divides the finite part, and membership in the finite part is
  detected by those prime powers.
* `TauCeti.GlobalNumberFields.Modulus.valued_eq_one_of_valued_sub_one_le`: an element of the
  `v`-adic completion congruent to one at a divisor of the finite part is a unit there.
* `TauCeti.GlobalNumberFields.congruenceSubgroup_le_primeToSubgroup`: an element congruent to one
  is a unit at every prime dividing the finite part.  This is what makes the ray a subgroup of the
  prime-to ideals.
* `TauCeti.GlobalNumberFields.IsCongrOne.mono` and
  `TauCeti.GlobalNumberFields.congruenceSubgroup_antitone`: congruence to one is antitone in the
  modulus, which is what makes the transition maps between ray class groups run from a larger
  modulus to a smaller one.
* `TauCeti.GlobalNumberFields.isCongrOne_narrowModulus_iff`: congruence to one modulo the modulus
  with unit finite part and every real place is total positivity.
* `TauCeti.GlobalNumberFields.unitsCongruenceSubgroup_narrowModulus`: the units congruent to one
  modulo the narrow modulus are the totally positive integer units.
* `TauCeti.GlobalNumberFields.Modulus.isCoprimeTo_of_dvd_span_singleton`: a divisor of a principal
  ideal whose generator is a unit at the finite part is prime to the modulus.
* `TauCeti.GlobalNumberFields.Modulus.isCoprimeTo_iff_sup_eq_top`: being prime to the support is
  comaximality with the finite part.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

 section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
section TauCeti.GlobalNumberFields
open TauCeti TauCeti.GlobalNumberFields



variable {K : Type*} [Field K] [NumberField K]

namespace TauCeti.GlobalNumberFields.Modulus
end TauCeti.GlobalNumberFields.Modulus
section Modulus
open TauCeti TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.Modulus



















































end Modulus









/-! ### Multiplicative congruence -/





namespace TauCeti.GlobalNumberFields.IsCongrOne
end TauCeti.GlobalNumberFields.IsCongrOne
section IsCongrOne
open TauCeti TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.IsCongrOne

variable {𝔪 : Modulus K} {x : Kˣ}











end IsCongrOne



































/-! ### Ideals prime to a modulus -/

theorem TauCeti.GlobalNumberFields.Modulus.isCoprimeTo_of_dvd_span_singleton {m : _root_.TauCeti.GlobalNumberFields.Modulus K} {J : _root_.Ideal (𝓞 K)}
    {a : 𝓞 K} {x : Kˣ} (hxa : (x : K) = a) (hx : x ∈ _root_.TauCeti.GlobalNumberFields.primeToSubgroup m)
    (hdvd : J ∣ _root_.Ideal.span {a}) : m.IsCoprimeTo J := by sorry
