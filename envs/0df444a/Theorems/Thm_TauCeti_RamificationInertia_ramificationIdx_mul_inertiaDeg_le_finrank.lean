-- Prove2me | Theorems.Thm_TauCeti_RamificationInertia_ramificationIdx_mul_inertiaDeg_le_finrank
-- name    : TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:46:45.215497+00:00
-- url     : https://prove2.me/theorems/1007d272-325f-463c-acc3-361bf78f0ce6
-- title:
--   The ramification-residue contribution is bounded by the module rank
-- statement:
--   Let $R$ be a commutative integral domain and let $S$ be a commutative finite flat $R$-algebra. For a prime $Q\subseteq S$ above a prime $P\subseteq R$,
--
--   $$
--   e(Q/P)f(Q/P)\le\operatorname{rank}_R S,
--   $$
--
--   where $e$ is the ideal ramification index and $f$ the residue-field degree.
--
--   This gives a uniform upper bound for the contribution of any one prime above the base prime.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/RamificationInertia/Tower.lean#L72-L88) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/RamificationInertia/Tower.lean#L72-L88

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_RamificationInertia_Tower
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.RamificationInertia.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ramification indices in finite flat towers

This file records consequences of the fundamental identity for ramification and inertia in a finite
flat extension of domains. The number of primes above a prime and each prime's contribution are at
most the rank of the extension. Ramification also cancels in a tower when the absolute ramification
index at the top equals the absolute ramification index at the intermediate prime: multiplicativity
then forces the relative ramification index to be one.

The cancellation result is the local step used in the finite-place half of the genus-field
construction. At a rational prime dividing a prime discriminant, both the quadratic base and the
prime-discriminant compositum have absolute ramification index two; cancellation then shows that
the compositum is unramified over the quadratic base.

## Main results

* `TauCeti.RamificationInertia.ncard_primesOver_le_finrank`: the number of primes above a prime is
  at most the rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank`: the contribution of one
  prime to the fundamental identity is at most the rank of the extension.
* `TauCeti.RamificationInertia.ramificationIdx_le_finrank`: a ramification index is at most the
  rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_eq_one_of_eq_ramificationIdx`: equal absolute
  ramification indices at two levels of a tower force relative ramification index one.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_eq_ramificationIdx`: if that equality
  holds at every prime above an intermediate prime, then the intermediate prime is unramified in
  the top ring.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_ramificationIdx_le`: it suffices to bound
  every absolute ramification index upstairs by the intermediate absolute ramification index.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_finrank_le_of_under_ramificationIdx_eq_one`: a
  transverse unramified subextension of sufficiently small relative degree supplies that bound.
* `TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn`: unramifiedness over the
  base descends from an integral extension to the subring below it, for `S` integral and
  torsion-free over the Dedekind domain `R`, with `R` and `S` both essentially of finite type over
  the base `A` and `A ≤ R ≤ S` a scalar tower. The base ring and the ideal are arbitrary.
-/

 section

open Ideal Module

namespace TauCeti.RamificationInertia
end TauCeti.RamificationInertia
section TauCeti.RamificationInertia
open TauCeti TauCeti.RamificationInertia

section Bounds

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Flat R S]

theorem TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank (p : _root_.Ideal R) [p.IsPrime]
    (q : _root_.Ideal S) [q.IsPrime] [q.LiesOver p] :
    q.ramificationIdx R * q.inertiaDeg R ≤ _root_.Module.finrank R S := by sorry
