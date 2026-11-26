-- Prove2me | Theorems.Thm_SemigroupBetti_beta1_le_two_mul_width
-- name    : SemigroupBetti.beta1_le_two_mul_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:16:11.895015+00:00
-- url     : https://prove2.me/theorems/c4f81f7c-65a6-4c3a-8d24-ecf73ca10428
-- title:
--   Semigroup Betti: beta1 le two mul width
-- statement:
--   The first Betti number is at most twice the width.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/Solution.lean#L92-L102
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/Solution.lean#L92-L102

module
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Definitions.Def_SemigroupBetti
public import Definitions.Def_SemigroupBetti_Solution
set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open MvPolynomial

theorem SemigroupBetti.beta1_le_two_mul_width (K : Type*) [Field K] (n : Fin 4 → ℕ)
    (hpos : 0 < n 0) (hmono : StrictMono n) (hgcd : Finset.univ.gcd n = 1)
    (hmin : MinimallyGenerates n) :
    (toricIdeal K n).spanRank ≤ (2 * (n 3 - n 0) : ℕ) := by sorry
