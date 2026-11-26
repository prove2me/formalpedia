-- Prove2me | Theorems.Thm_SemigroupBetti_beta1_le_two_mul_normalizedWidth
-- name    : SemigroupBetti.beta1_le_two_mul_normalizedWidth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:15:23.187088+00:00
-- url     : https://prove2.me/theorems/7ba3da6c-0743-5f96-b6db-812a1b7937ca
-- title:
--   Semigroup Betti: beta1 le two mul normalized Width
-- statement:
--   **Main theorem.** For a minimally four-generated numerical semigroup, the first Betti number
--   is at most `2W`, `W` the normalized width.
--
--   Source: https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/Solution.lean#L79-L89
-- source:
--   https://github.com/BenKeene/semigroup-betti/blob/c94da4f5cb07e2ccf62c9ae18887aedd73e95bf2/Solution.lean#L79-L89

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

theorem SemigroupBetti.beta1_le_two_mul_normalizedWidth (K : Type*) [Field K] (n : Fin 4 → ℕ)
    (hpos : 0 < n 0) (hmono : StrictMono n) (hgcd : Finset.univ.gcd n = 1)
    (hmin : MinimallyGenerates n) :
    (toricIdeal K n).spanRank ≤ (2 * normalizedWidth n : ℕ) := by sorry
