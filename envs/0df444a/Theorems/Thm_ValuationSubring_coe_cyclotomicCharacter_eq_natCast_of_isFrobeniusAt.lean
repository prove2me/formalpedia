-- Prove2me | Theorems.Thm_ValuationSubring_coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt
-- name    : ValuationSubring.coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/98e5c818-ba45-5f91-8ef6-79b717b80314
-- title:
--   Cyclotomic character of Frobenius at ℓ ≠ p equals ℓ
-- statement:
--   Let $p$ be a prime and let $\ell$ be a prime with $\ell \neq p$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which satisfies `A.LiesOverPrime ℓ`, that is, the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$ (so $\ell$ lies in the maximal ideal of $A$). Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ satisfying `A.IsFrobeniusAt σ ℓ`, i.e. $\sigma$ belongs to the decomposition subgroup of $A$ over $\mathbb{Q}$ (it preserves $A$) and the element of that subgroup determined by $\sigma$ acts on the residue field of $A$ by $x \mapsto x^{\ell}$ for every $x$. The conclusion is that the value of the $p$-adic cyclotomic character of $\overline{\mathbb{Q}}$ at the ring isomorphism underlying $\sigma$, an element of $\mathbb{Z}_p^{\times}$, is equal, as an element of $\mathbb{Z}_p$, to the image of the natural number $\ell$.
--
--   This is the standard computation of the $p$-adic cyclotomic character on an arithmetic Frobenius element at a place of $\overline{\mathbb{Q}}$ above a prime $\ell \neq p$. It is used wherever determinants of $p$-adic Galois representations attached to modular forms or elliptic curves are evaluated at Frobenius elements, for instance in the identification of the determinant of an adic Galois representation at primes not dividing the conductor and in the analysis of characteristic polynomials of inertia.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt.lean

import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.coe_cyclotomicCharacter_eq_natCast_of_isFrobeniusAt
    {p : ℕ} [Fact p.Prime] {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ) :
    ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = ℓ := by sorry
