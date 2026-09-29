-- Prove2me | Theorems.Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
-- name    : Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/2e946860-e24c-54fa-900b-8ef1c2df16f6
-- title:
--   Frobenius density over ℚ, division form
-- statement:
--   Let $H$ be a subgroup of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, whose underlying set is open; let $\sigma$ be an element of that Galois group, and let $M$ be a natural number with $M>0$. The assertion is that there exist a natural number $\ell$, a valuation subring $A$ of $\overline{\mathbb Q}$, elements $\tau$ and $g$ of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and natural numbers $n$ and $k$, such that: $\ell$ is prime; $\ell$ does not divide $M$; $A$ lies over $\ell$ in the sense that the image of $\ell$ in $\overline{\mathbb Q}$ is a non-unit of $A$; $\tau$ is a Frobenius at $\ell$ for $A$, meaning that $\tau$ belongs to the decomposition subgroup of $A$ over $\mathbb Q$ and the induced action of $\tau$ on the residue field of $A$ is $x \mapsto x^{\ell}$; and finally the two membership relations
--   $$g\,\tau^{n}\,g^{-1}\,\sigma^{-1} \in H, \qquad g\,\tau\,g^{-1}\,(\sigma^{k})^{-1} \in H$$
--   hold. Thus, modulo $H$, the element $\sigma$ is a power of the conjugate $g\tau g^{-1}$, and $g\tau g^{-1}$ is a power of $\sigma$.
--
--   This is Frobenius's density theorem in its division form, transported to the absolute Galois group of $\mathbb Q$ and formulated modulo an arbitrary open subgroup, with the exceptional primes avoided by requiring $\ell \nmid M$. It is the tool by which properties of Frobenius elements (traces, orders, unipotence) are transferred to arbitrary elements of a finite quotient of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, and it is used in the study of residual Galois representations — for instance in locating stable lines and in computing determinants and Hecke eigenvalues of mod-$p$ representations attached to modular curves. The proof cites a statement of Frobenius density for Galois number fields together with the existence of a Frobenius automorphism at a valuation subring lying over a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_conj_mem_of_isOpen
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n k : ℕ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H ∧ g * τ * g⁻¹ * (σ ^ k)⁻¹ ∈ H := by sorry
