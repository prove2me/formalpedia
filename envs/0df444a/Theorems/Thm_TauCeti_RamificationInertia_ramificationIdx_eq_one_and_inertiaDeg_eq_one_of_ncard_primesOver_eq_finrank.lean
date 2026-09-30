-- Prove2me | Theorems.Thm_TauCeti_RamificationInertia_ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
-- name    : TauCeti.RamificationInertia.ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:40:15.744865+00:00
-- url     : https://prove2.me/theorems/00e84454-d64a-4dab-9503-72cc641ef5c7
-- title:
--   A maximal prime-fiber count forces unit ramification and residue degrees
-- statement:
--   Let $R$ be a commutative integral domain and let $S$ be a commutative $R$-algebra that is finite and flat as an $R$-module. Let $P\subseteq R$ be prime and let $Q\subseteq S$ be prime above $P$. If the number of primes of $S$ above $P$ equals the module rank $n=\operatorname{rank}_R S$, then
--
--   $$
--   e(Q/P)=1\qquad\text{and}\qquad f(Q/P)=1.
--   $$
--
--   Here $e$ is the ideal ramification index and $f$ the residue-field degree.
--
--   This extracts the local indices from complete splitting expressed solely as a maximal number of prime ideals.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/RamificationInertia/Splitting.lean#L47-L73) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/RamificationInertia/Splitting.lean#L47-L73

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.RamificationInertia.Basic

section
set_option autoImplicit true
namespace TauCeti.RamificationInertia
end TauCeti.RamificationInertia
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Complete splitting is trivial ramification and inertia

This file records the non-Galois counting criterion for primes in finite flat extensions of
domains: a prime has as many primes above it as the degree allows exactly when every one of them
is unramified with trivial residue extension.

The Galois form, where the count is compared with the order of the Galois group, is in
`TauCeti/NumberTheory/RamificationInertia/Galois.lean`. No Galois hypothesis is needed here:
the fundamental identity alone forces each summand `e * f` down to `1`.

## Main results

* `ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank` — a maximal count
  of primes above `P` makes `e = f = 1` at each of them.
* `Ideal.ncard_primesOver_eq_finrank_iff_forall_ramificationIdx_eq_one_and_inertiaDeg_eq_one` —
  conversely, `e = f = 1` at every prime above `P` makes the count maximal.
* `bijective_algebraMap_quotient_of_ncard_primesOver_eq_finrank` — for `P` maximal, the same count
  makes the residue map `R ⧸ P → S ⧸ Q` bijective.

## Provenance

Built directly on Mathlib's fundamental identity for finite flat extensions of domains
(`Ideal.sum_ramification_inertia_eq_finrank`). The residue-field consequence additionally uses
Mathlib's identification of the inertia degree with the rank of the residue extension
(`Ideal.inertiaDeg'_algebraMap`) and its characterisation of rank-one algebras over a field
(`Algebra.finrank_eq_one_iff_bijective_algebraMap`).
-/

 section

open Ideal Module

namespace TauCeti.RamificationInertia
end TauCeti.RamificationInertia
section TauCeti.RamificationInertia
open TauCeti TauCeti.RamificationInertia

theorem TauCeti.RamificationInertia.ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
    {R S : Type*} [_root_.CommRing R] [_root_.IsDomain R] [_root_.CommRing S] [_root_.Algebra R S] [_root_.Module.Finite R S]
    [_root_.Module.Flat R S] (P : _root_.Ideal R) [P.IsPrime] (Q : _root_.Ideal S)
    [Q.IsPrime] [Q.LiesOver P] (hsplit : (P.primesOver S).ncard = _root_.Module.finrank R S) :
    Q.ramificationIdx R = 1 ∧ Q.inertiaDeg R = 1 := by sorry
