-- Prove2me | Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
-- name    : ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/dc484373-40d7-5d04-b85a-b6ee66ec5301
-- title:
--   Existence of a Frobenius element at a place above q
-- statement:
--   Let $q$ be a prime number and let $A$ be a valuation subring of an algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$, assumed to lie over $q$ in the sense that the image of $q$ in $\overline{\mathbb{Q}}$ belongs to the set of nonunits of $A$ (equivalently, $q$ lies in the maximal ideal of the valuation ring $A$). The conclusion asserts the existence of a field automorphism $\varphi$ of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$, i.e. an element of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, which is a Frobenius element at $A$ for the exponent $q$: that is, $\varphi$ lies in the decomposition subgroup of $A$ relative to $\mathbb{Q}$ (the subgroup of those $\mathbb{Q}$-automorphisms whose natural action fixes the valuation subring $A$), and the induced action of $\varphi$, viewed as an element of that decomposition subgroup, on the residue field of the local ring $A$ sends every element $x$ to $x^{q}$.
--
--   This is the classical existence of a Frobenius element at a place of $\overline{\mathbb{Q}}$ above a rational prime, i.e. the surjectivity of the decomposition group onto the Galois group of the residue field extension. It is what allows traces of Frobenius at good primes to be spoken of unambiguously, and it is invoked throughout the formalisation wherever Galois representations attached to newforms or to elliptic curves are evaluated at a Frobenius element, including the comparison of Frobenius eigenvalues with Hecke eigenvalues and the analysis of inertia at primes of bad reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime {q : ℕ} (hq : q.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) : ∃ φ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), A.IsFrobeniusAt φ q := by sorry
