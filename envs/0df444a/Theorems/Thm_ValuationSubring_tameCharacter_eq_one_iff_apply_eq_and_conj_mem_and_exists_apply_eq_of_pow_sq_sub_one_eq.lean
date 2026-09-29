-- Prove2me | Theorems.Thm_ValuationSubring_tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
-- name    : ValuationSubring.tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/975d49aa-7d7a-598c-b3ea-848500d82371
-- title:
--   Kernel, conjugates and values of the level-two tame character
-- statement:
--   Let $q$ be a prime number, let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense that the image of $q$ in $\overline{\mathbb{Q}}$ belongs to `P.nonunits`, and let $\pi \in \overline{\mathbb{Q}}$ satisfy $\pi^{q^2-1} = q$. Write $\theta(\tau) =$ `P.tameCharacter π τ` for the element of the residue field of $P$ defined as the residue of $\tau\pi/\pi$ when $\tau\pi/\pi \in P$, and as $0$ otherwise. Then three assertions hold simultaneously. First, for every $\tau \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ one has $\theta(\tau) = 1$ if and only if $\tau\pi = \pi$. Second, for every $\sigma$ in the decomposition subgroup of $P$ over $\mathbb{Q}$ and every $\tau$ in `P.inertiaSubgroupIn ℚ`, the image of the inertia subgroup of $P$ inside the full Galois group under the inclusion of the decomposition subgroup, if $\theta(\tau) = 1$ then $\sigma\tau\sigma^{-1}$ again lies in `P.inertiaSubgroupIn ℚ` and $\theta(\sigma\tau\sigma^{-1}) = 1$. Third, for every ring homomorphism $\iota$ from the field `GaloisField q 2` with $q^2$ elements into the residue field of $P$, and every $\tau \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, there exists $\alpha \in$ `GaloisField q 2` with $\iota(\alpha) = \theta(\tau)$.
--
--   This collects the basic properties of Serre's fundamental tame character of level two attached to the uniformiser $\pi$ with $\pi^{q^2-1} = q$: its kernel is the stabiliser of $\pi$, the condition $\theta = 1$ is stable under conjugation by the decomposition group, and its values are accounted for by the field of $q^2$ elements. It is used in the construction of Galois-equivariant charts on modular curves at full level, notably by the statements producing semistable coverings with prescribed reduction on the Igusa domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq.lean

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.FieldTheory.Finite.GaloisField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem
ValuationSubring.tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) :
    (∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.tameCharacter π τ = 1 ↔ τ π = π) ∧
    (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 →
      σ * τ * σ⁻¹ ∈ P.inertiaSubgroupIn ℚ ∧ P.tameCharacter π (σ * τ * σ⁻¹) = 1) ∧
    (∀ ι : GaloisField q 2 →+* IsLocalRing.ResidueField P,
      ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ α : GaloisField q 2, ι α = P.tameCharacter π τ) := by sorry
