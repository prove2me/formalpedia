-- Prove2me | Theorems.Thm_SelbergSieve_siftedSum_le_mainSum_errSum_of_UpperBoundSieve
-- name    : SelbergSieve.siftedSum_le_mainSum_errSum_of_UpperBoundSieve
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:53:59.384102+00:00
-- url     : https://prove2.me/theorems/031d47d7-0024-4ee2-94dc-9db2fb283e07
-- title:
--   Sifted sum bounded by main term plus error sum for any upper-bound sieve $\mu^{+}$
-- statement:
--   Work in the axiomatic sieve setting: a finite weighted set $A$ with nonnegative weights and total approximate mass $X$, a squarefree product $P$ of sieving primes, a multiplicative density $\nu$, and remainders $R_d$. An *upper bound sieve* is a function $\mu^{+}$ on the natural numbers satisfying the pointwise majorization $\sum_{d \mid n} \mu^{+}(d) \ge \mathbf{1}_{n = 1}$ evaluated at $\gcd(n, P)$, so that $\mu^{+}$ dominates the indicator of being coprime to $P$.
--
--   For any such upper bound sieve $\mu^{+}$, the sifted sum $S(A, P)$ (the total weight of elements of $A$ coprime to $P$) satisfies
--
--   $$S(A, P) \;\le\; X \cdot M(\mu^{+}) \;+\; E(\mu^{+}),$$
--
--   where $M(\mu^{+}) = \sum_{d \mid P} \mu^{+}(d)\, \nu(d)$ is the *main sum* and $E(\mu^{+}) = \sum_{d \mid P} |\mu^{+}(d)|\, |R_d|$ is the *error sum* of the sieve weights.
--
--   This is the basic decomposition step common to all upper-bound sieves (Selberg, Brun, beta-sieve, ...): once the combinatorial majorant $\mu^{+}$ is fixed, the sifting problem splits into a density main term proportional to $X$ and an arithmetic error term. In the formal development it is the interface through which the optimized Selberg weights are fed to produce the fundamental Selberg bound.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Basic.lean#L150-L152

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Definitions.Def_Sieve_AuxResults_defs
import Definitions.Def_Sieve_Basic_defs

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

open SelbergSieve

variable (s : BoundingSieve)
local notation3 "ν" => BoundingSieve.nu (self := s)
local notation3 "P" => BoundingSieve.prodPrimes (self := s)
local notation3 "a" => BoundingSieve.weights (self := s)
local notation3 "X" => BoundingSieve.totalMass (self := s)
local notation3 "A" => BoundingSieve.support (self := s)
local notation3 "𝒜" => BoundingSieve.multSum (s := s)
local notation3 "R" => BoundingSieve.rem (s := s)

-- S = ∑_{l|P, l≤√y} g(l)
-- Used in statement of the simple form of the selberg bound

local notation3 "g" => SelbergSieve.selbergTerms s

local notation "δ" => delta

theorem SelbergSieve.siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ X * mainSum (s := s) μPlus + errSum (s := s) μPlus := by sorry
