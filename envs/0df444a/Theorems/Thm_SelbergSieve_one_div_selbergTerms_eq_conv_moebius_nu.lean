-- Prove2me | Theorems.Thm_SelbergSieve_one_div_selbergTerms_eq_conv_moebius_nu
-- name    : SelbergSieve.one_div_selbergTerms_eq_conv_moebius_nu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:52:34.28654+00:00
-- url     : https://prove2.me/theorems/c3a86ae1-8b61-4642-b1f2-5cd85df327ed
-- title:
--   Möbius inversion for the Selberg sieve terms: $1/g(l) = \sum_{d \mid l} \mu(l/d)\, \nu(d)^{-1}$
-- statement:
--   Work in the setting of a Selberg sieve with multiplicative density function $\nu$ and associated *Selberg terms* $g$, the multiplicative function given on squarefree arguments by $g(l) = \nu(l) \prod_{p \mid l} (1 - \nu(p))^{-1}$.
--
--   Let $l$ be a squarefree natural number with $\nu(l) \neq 0$. Then the reciprocal of the Selberg term at $l$ is the Möbius transform of the reciprocal of the density:
--
--   $$\frac{1}{g(l)} \;=\; \sum_{d \mid l} \mu\!\left(\frac{l}{d}\right) \frac{1}{\nu(d)},$$
--
--   where $\mu$ is the Möbius function and the sum runs over all divisors $d$ of $l$.
--
--   This is the Möbius-inversion companion of the identity $\nu(d)^{-1} = \sum_{l \mid d} 1/g(l)$. Together the two identities express that $1/g$ and $1/\nu$ are related by Dirichlet convolution with $\mu$, the algebraic mechanism behind the diagonalization of Selberg's quadratic form and the appearance of the bounding sum $S = \sum_{l} g(l)$ in the main term of the sieve.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Basic.lean#L98-L113

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

theorem SelbergSieve.one_div_selbergTerms_eq_conv_moebius_nu (l : ℕ) (hl : Squarefree l)
    (hnu_nonzero : ν l ≠ 0) : 1 / g l = ∑ d ∈ l.divisors, (μ <| l / d) * (ν d)⁻¹ := by sorry
