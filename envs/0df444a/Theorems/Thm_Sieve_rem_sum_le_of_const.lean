-- Prove2me | Theorems.Thm_Sieve_rem_sum_le_of_const
-- name    : Sieve.rem_sum_le_of_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:55:27.98496+00:00
-- url     : https://prove2.me/theorems/d9bf4521-9fbf-40f6-b25d-cb22f712cd9c
-- title:
--   Uniform remainder bound: $\sum_{d \le y,\, d \mid P} 3^{\omega(d)}|R_d| \le C\, y\, (1 + \log y)^3$
-- statement:
--   Let $s$ be a Selberg sieve with squarefree sieving modulus $P$, level $y$, and remainder terms $R_d$ (the error in approximating the weight of the elements of the sifted set divisible by $d$ by $\nu(d) X$). Suppose the remainders are uniformly bounded: there is a constant $C$ with $|R_d| \le C$ for every $d > 0$. Write $\omega(d)$ for the number of distinct prime factors of $d$.
--
--   Then the standard $3^{\omega}$-weighted error sum of the fundamental Selberg bound satisfies
--
--   $$\sum_{\substack{d \mid P \\ d \le y}} 3^{\omega(d)}\, |R_d| \;\le\; C\, y\, (1 + \log y)^3.$$
--
--   The point is that $3^{\omega(d)}$ is the number of ways to write $d$ as an ordered product of three factors, so its sum over $d \le y$ is a triple divisor sum of size $O(y \log^3 y)$. This lemma turns the abstract error term of the Selberg sieve into an explicit polynomial-in-$\log$ bound whenever each individual remainder is $O(1)$ — the situation for sieving an interval, where $R_d$ is a rounding error. It is the final estimate needed to make the Brun–Titchmarsh-type applications of the sieve fully explicit.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/SelbergBounds.lean#L511-L526

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

open CompletelyMultiplicative
open ArithmeticFunction

/-
Proposed generalisation :

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve)
    (hnu : CompletelyMultiplicative s.nuDivSelf) (hnu_nonneg : ∀ n, 0 ≤ s.nuDivSelf n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nuDivSelf p < 1):
    s.selbergBoundingSum ≥ ∑ m in
      (Finset.Icc 1 (Nat.floor <| Real.sqrt s.level)).filter (fun m => ∀ p, p.Prime → p ∣ m → p ∣ s.prodPrimes),
      s.nu m
-/

open ArithmeticFunction

theorem Sieve.rem_sum_le_of_const (s : SelbergSieve) (C : ℝ) (hrem : ∀ d > 0, |rem (s := s.toBoundingSieve) d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors, (if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0)
      ≤ C * s.level * (1+Real.log s.level)^3 := by sorry
