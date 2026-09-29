-- Prove2me | Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
-- name    : ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/8fffe60a-526e-5a93-b169-b040f7109c94
-- title:
--   Existence of a place above p with a Frobenius element
-- statement:
--   Let $p$ be a prime number (an element of `Nat.Primes`). The assertion is that there exist a valuation subring $A$ of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` and a $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ such that two conditions hold. First, $A$ lies over $p$ in the sense of the project predicate `LiesOverPrime`: the image of the natural number $p$ in $\overline{\mathbb{Q}}$ belongs to `A.nonunits`, the set of elements of $\overline{\mathbb{Q}}$ of valuation less than $1$ for the valuation attached to $A$, i.e. $p$ lies in the maximal ideal of $A$. Second, $\sigma$ is a Frobenius element at $A$ for the exponent $p$ in the sense of `IsFrobeniusAt`: $\sigma$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ (the stabiliser of $A$ among the $\mathbb{Q}$-automorphisms), and the induced action of $\sigma$ on the residue field `IsLocalRing.ResidueField A` sends every element $x$ to $x^{p}$.
--
--   This is the standard existence statement underlying the definition of Frobenius elements in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$: every rational prime admits a place of $\overline{\mathbb{Q}}$ above it, and the decomposition group at such a place contains an element inducing the $p$-power map on the residue field. It is the entry point for the computations of Frobenius traces and Euler factors of Galois representations attached to elliptic curves and modular forms elsewhere in the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

theorem ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
    (p : Nat.Primes) :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      A.LiesOverPrime (p : ℕ) ∧ A.IsFrobeniusAt σ (p : ℕ) := by sorry
