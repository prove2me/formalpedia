-- Prove2me | Theorems.Thm_TauCeti_NumberField_card_primesOverFinset_le_finrank
-- name    : TauCeti.NumberField.card_primesOverFinset_le_finrank
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:39:29.352985+00:00
-- url     : https://prove2.me/theorems/5031b2a3-fa74-4440-a8c4-b00649bf2e01
-- title:
--   At most the field degree many primes lie above a rational prime
-- statement:
--   Let $K$ be a number field and let $p$ be a rational prime. Then
--
--   $$
--   \#\{\mathfrak q\subseteq\mathcal O_K:\mathfrak q\text{ prime},\ \mathfrak q\cap\mathbb Z=p\mathbb Z\}\le[K:\mathbb Q].
--   $$
--
--   This uniformly bounds fibers of contraction from number-field primes to rational primes.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/PrimeIdeal.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/PrimeIdeal.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Unramified.Locus

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Prime ideals of rings of integers

This file records general utilities for the prime ideals of a number field above a rational
prime: packaging them as non-zero-divisors so that their classes can be taken with
`ClassGroup.mk0`, counting them, and factoring an unramified rational prime into them.

## Main results

* `NumberField.mem_nonZeroDivisors_of_prime_of_liesOver`: a prime ideal above a rational prime is
  a non-zero-divisor in the ideal monoid.
* `NumberField.exists_primeIdealFamily`: a finite set of rational primes admits a family of prime
  ideals above it, packaged for `ClassGroup.mk0`.
* `TauCeti.NumberField.card_primesOverFinset_le_finrank`: at most `[K : ℚ]` primes of `𝓞 K`
  lie over a nonzero prime of `ℤ`.
* `TauCeti.NumberField.span_natCast_eq_prod_primesOverFinset`: a rational prime unramified in
  `K` generates the squarefree product of the primes of `𝓞 K` above it.
-/

 section

open NumberField Ideal
open scoped NumberField nonZeroDivisors

namespace NumberField
end NumberField
section NumberField
open NumberField

variable {K : Type*} [Field K] [NumberField K]





end NumberField

namespace TauCeti.NumberField
end TauCeti.NumberField
section TauCeti.NumberField
open TauCeti TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem TauCeti.NumberField.card_primesOverFinset_le_finrank {p : _root_.Ideal ℤ} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (_root_.IsDedekindDomain.primesOverFinset p (𝓞 K)).card ≤ _root_.Module.finrank ℚ K := by sorry
