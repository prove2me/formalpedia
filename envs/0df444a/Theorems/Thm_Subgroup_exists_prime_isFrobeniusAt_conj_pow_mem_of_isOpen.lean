-- Prove2me | Theorems.Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
-- name    : Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/f4db96fe-87d5-55f5-9653-0e0315e04195
-- title:
--   Frobenius density modulo an open subgroup of Gal(ℚ̄/ℚ)
-- statement:
--   Let $H$ be a subgroup of the absolute Galois group $\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$, realised as the group of $\mathbf Q$-algebra automorphisms of `AlgebraicClosure ℚ`, and assume that the underlying set of $H$ is open for the Krull topology. Let $\sigma$ be an element of this Galois group and let $M$ be a natural number with $0 < M$. The assertion is that there exist a natural number $\ell$, a valuation subring $A$ of $\overline{\mathbf Q}$, two Galois elements $\tau$ and $g$, and an exponent $n \in \mathbf N$, such that: $\ell$ is prime; $\ell$ does not divide $M$; $A$ satisfies `LiesOverPrime ℓ`, that is, the image of $\ell$ in $\overline{\mathbf Q}$ is a non-unit of $A$; $A$ satisfies `IsFrobeniusAt τ ℓ`, that is, $\tau$ belongs to the decomposition subgroup of $A$ over $\mathbf Q$ (so $\tau$ preserves $A$) and the induced action of $\tau$ on the residue field of $A$ is $x \mapsto x^{\ell}$; and finally $g \tau^{n} g^{-1} \sigma^{-1} \in H$, i.e. $\sigma$ and the conjugate power $g\tau^{n}g^{-1}$ agree modulo $H$.
--
--   This is the qualitative form of Frobenius' density theorem (the cyclic-subgroup predecessor of Chebotarev's theorem) for $\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)$: modulo any open subgroup, every Galois element is conjugate to a power of a Frobenius element at a place above a prime avoiding the prime divisors of a prescribed positive integer $M$. It is the density input for the Brauer–Nesbitt style arguments in which Frobenius traces determine a Galois representation, and is cited in the identification of determinants with powers of the cyclotomic character, in the recognition of representations up to conjugacy from Frobenius characteristic polynomials, and in the Hecke-algebra construction used for non-Eisenstein primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subgroup_exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen.lean

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hH : IsOpen (H : Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {M : ℕ} (hM : 0 < M) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (n : ℕ),
      ℓ.Prime ∧ ¬ ℓ ∣ M ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        g * τ ^ n * g⁻¹ * σ⁻¹ ∈ H := by sorry
