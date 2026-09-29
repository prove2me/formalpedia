-- Prove2me | Theorems.Thm_Sieve_prime_dvd_primorial_iff
-- name    : Sieve.prime_dvd_primorial_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:55:05.923802+00:00
-- url     : https://prove2.me/theorems/cd28b662-6aaf-49bb-a80c-a42ff6af852e
-- title:
--   A prime divides the primorial $n\#$ if and only if $p \le n$
-- statement:
--   Let $n$ be a natural number and let $p$ be a prime. Recall that the *primorial* $n\# = \prod_{q \le n,\ q \text{ prime}} q$ is the product of all primes not exceeding $n$.
--
--   Then divisibility of the primorial by $p$ is characterized exactly by the size of $p$:
--
--   $$p \mid n\# \;\Longleftrightarrow\; p \le n.$$
--
--   This elementary characterization is the bookkeeping fact needed when the squarefree sieving modulus $P$ of a sieve is chosen to be a primorial: it identifies the set of primes the sieve removes as precisely the primes up to $n$. In the PNT+ Selberg sieve development it feeds the identification of the sifted sum as a count of $z$-rough numbers (numbers free of prime factors $\le z$).
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/SelbergBounds.lean#L63-L77

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Batteries.Tactic.Lemma
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.SelbergSieve
import Definitions.Def_Sieve_AuxResults_defs
import Definitions.Def_Sieve_Basic_defs
import Definitions.Def_Sieve_SelbergBounds_defs
import Definitions.Def_Sieve_Selberg_defs
/-!
# Bounds for the Selberg sieve
This file proves a number of results to help bound `Sieve.selbergSum`

## Main Results
* `selbergBoundingSum_ge_sum_div`: If `ν` is completely multiplicative then `S ≥ ∑_{n ≤ √y}, ν n`
* `boundingSum_ge_log`: If `ν n = 1 / n` then `S ≥ log y / 2`
* `rem_sum_le_of_const`: If `R_d ≤ C` then the error term is at most `C * y * (1 + log y)^3`
-/

set_option lang.lemmaCmd true

open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve

open Sieve

theorem Sieve.prime_dvd_primorial_iff (n p : ℕ) (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by sorry
