-- Prove2me | Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
-- name    : ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/f8354cc0-dcd4-56ac-9e2a-1b188a48da2d
-- title:
--   Existence of a Frobenius element at a place of ℚ̄ above p
-- statement:
--   Let $p$ be a natural number which is prime, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Assume `A.LiesOverPrime p`, that is, the image of $p$ in $\overline{\mathbb{Q}}$ belongs to `A.nonunits`, the non-units of $A$ (equivalently, $p$ lies in the maximal ideal of the valuation ring $A$, so the place $A$ lies over the rational prime $p$). The assertion is that there exists a $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ with `A.IsFrobeniusAt σ p`, which by definition means: $\sigma$ belongs to the decomposition subgroup of $A$ over $\mathbb{Q}$, i.e. $\sigma$ stabilises $A$ as a subring of $\overline{\mathbb{Q}}$, and the resulting action of $\sigma$, viewed as an element of that decomposition subgroup, on the residue field `IsLocalRing.ResidueField A` satisfies $\sigma \cdot x = x^{p}$ for every $x$ in the residue field.
--
--   This is the existence of a Frobenius element at a place of $\overline{\mathbb{Q}}$ above a rational prime, the statement that makes the Frobenius conjugacy class at $p$ available for Galois representations attached to elliptic curves and modular forms. It is used throughout the project wherever Frobenius traces and characteristic polynomials at a prime are compared with Hecke eigenvalues, for instance in the analysis of eigenforms and of inertia at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
    {p : ℕ} (hp : p.Prime) {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime p) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p := by sorry
