-- Prove2me | Theorems.Thm_SelbergSieve_lambdaSquared_eq_zero_of_support
-- name    : SelbergSieve.lambdaSquared_eq_zero_of_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:53:24.860226+00:00
-- url     : https://prove2.me/theorems/c3b6884c-4cdb-4887-a829-71f9e1c21e00
-- title:
--   Support of the $\Lambda^2$ sieve weights: $\lambda^2_w(d)=0$ for $d>y$ when $w$ is supported on $d^2\le y$
-- statement:
--   Let $w\colon\mathbb{N}\to\mathbb{R}$ be a weight function and $y\in\mathbb{R}$ a level. The Selberg $\Lambda^2$ weights are defined by
--
--   $$\lambda^{2}_{w}(d) \;=\; \sum_{\substack{d_1,\,d_2\\ [d_1,d_2]=d}} w(d_1)\,w(d_2),$$
--
--   the sum over pairs whose least common multiple is $d$. Suppose $w$ is supported on the range $d^{2}\le y$, i.e. $w(d)=0$ whenever $d^{2}>y$. Then for every $d$ with $d>y$,
--
--   $$\lambda^{2}_{w}(d) \;=\; 0.$$
--
--   The reason is that any pair $d_1,d_2$ in the support of $w$ satisfies $d_1,d_2\le\sqrt{y}$, hence $[d_1,d_2]\le d_1 d_2\le y$; so no pair can produce an lcm exceeding $y$.
--
--   This support lemma expresses the defining feature of Selberg's method: choosing the free weights $w$ up to level $\sqrt{y}$ guarantees the induced sieve weights $\lambda^2_w$ vanish beyond level $y$, so the error term of the sieve involves only moduli $d\le y$. It is what makes the level-of-distribution bookkeeping of the Selberg sieve (and its applications such as Brun–Titchmarsh) go through.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Basic.lean#L176-L200

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

-- Unused ?

-- Facts about g

-- Results about Lambda Squared Sieves

theorem SelbergSieve.lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by sorry
