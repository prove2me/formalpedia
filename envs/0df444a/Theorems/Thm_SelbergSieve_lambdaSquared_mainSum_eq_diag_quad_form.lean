-- Prove2me | Theorems.Thm_SelbergSieve_lambdaSquared_mainSum_eq_diag_quad_form
-- name    : SelbergSieve.lambdaSquared_mainSum_eq_diag_quad_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:53:41.992682+00:00
-- url     : https://prove2.me/theorems/f7e7ef20-2042-4aee-a40e-ab3ab868789e
-- title:
--   Selberg diagonalization: the $\Lambda^2$ main term equals $\sum_{l\mid P} \frac{1}{g(l)}\bigl(\sum_{l\mid d} \nu(d)w(d)\bigr)^2$
-- statement:
--   Work in the Selberg sieve formalism: a sieve problem $s$ carries a squarefree level $P$, a multiplicative density $\nu$, and the Selberg terms $g(l)=\nu(l)\prod_{p\mid l}(1-\nu(p))^{-1}$. For a weight function $w\colon\mathbb{N}\to\mathbb{R}$, let $\lambda^2_w(d)=\sum_{[d_1,d_2]=d}w(d_1)w(d_2)$ be the induced $\Lambda^2$ weights, and let the main sum be the quadratic form these weights produce in the sieve's main term, $\sum_{d_1,d_2\mid P}\nu([d_1,d_2])\,w(d_1)w(d_2)$. Then the main sum diagonalizes as a weighted sum of squares over divisors of $P$:
--
--   $$\mathrm{mainSum}\bigl(\lambda^{2}_{w}\bigr) \;=\; \sum_{l\,\mid\, P} \frac{1}{g(l)} \left( \sum_{\substack{d\,\mid\, P\\ l\,\mid\, d}} \nu(d)\,w(d) \right)^{\!2}.$$
--
--   This is Selberg's celebrated diagonalization of the sieve quadratic form: using the identity $\nu([d_1,d_2])=\nu(d_1)\nu(d_2)/\nu((d_1,d_2))$ and the divisor-sum identity $\sum_{l\mid d}g(l)=g(d)/\nu(d)$, the double sum over pairs $(d_1,d_2)$ is re-expressed as a positive-definite diagonal form in the linear combinations $y_l=\sum_{l\mid d}\nu(d)w(d)$.
--
--   Its significance is that it turns the sieve optimization into an elementary least-squares problem: the diagonal form is minimized subject to the normalization $w(1)=1$ by an explicit choice of $y_l$, yielding the Selberg sieve upper bound with main-term constant $1/\sum_{l\le\sqrt y}g(l)$ — the route to Brun–Titchmarsh-type theorems in this development.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/Basic.lean#L260-L283

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

theorem SelbergSieve.lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ l ∈ divisors P,
        1 / g l * (∑ d ∈ divisors P, if l ∣ d then ν d * w d else 0) ^ 2 := by sorry
