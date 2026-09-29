-- Prove2me | Theorems.Thm_ValuationSubring_exists_monoidHom_galoisField_units_forall_tameCharacter_eq_imp_eq_or_eq_pow
-- name    : ValuationSubring.exists_monoidHom_galoisField_units_forall_tameCharacter_eq_imp_eq_or_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/aa359ff5-e971-5d69-addb-33364d94b6e4
-- title:
--   Tame inertia labels come from a character of 𝔽_{q²}^×
-- statement:
--   Let $q$ be a prime, let $P$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$ (so $P$ lies over $q$), and write $I_P \subseteq \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ for the image in the full Galois group of the inertia subgroup of the decomposition subgroup of $P$, and $k_P$ for the residue field of $P$. For $\pi \in \overline{\mathbb{Q}}$ and $\sigma$ in the Galois group, $P.\mathrm{tameCharacter}\,\pi\,\sigma$ denotes the residue of $\sigma(\pi)/\pi$ when that quotient lies in $P$, and $0$ otherwise. Let $O''$ be an integral domain and $a$ any function from the Galois group to $(O'')^\times$ which is multiplicative on $I_P$, i.e. $a(\sigma\tau)=a(\sigma)a(\tau)$ for $\sigma,\tau \in I_P$, and satisfies $a(\sigma)^{q^2-1}=1$ for $\sigma \in I_P$. The assertion is that there exists a monoid homomorphism $\theta : \mathbb{F}_{q^2}^\times \to (O'')^\times$ such that: (i) for every $\pi$ with $\pi^{q^2-1}=q$ and every ring homomorphism $\iota : \mathbb{F}_{q^2} \to k_P$, either $a(\sigma)=\theta(\alpha)$ whenever $\sigma \in I_P$, $\alpha \in \mathbb{F}_{q^2}^\times$ and $\iota(\alpha)=P.\mathrm{tameCharacter}\,\pi\,\sigma$, or the same with $\theta(\alpha^q)$ in place of $\theta(\alpha)$ (which alternative holds may depend on $(\pi,\iota)$, but $\theta$ does not); (ii) some $\tau \in I_P$ has $a(\tau)^{q-1} \neq 1$ if and only if $\theta^q \neq \theta$ in the pointwise group structure; (iii) $a(\sigma)^{q+1}=1$ for all $\sigma \in I_P$ if and only if $\theta^{q+1}=1$.
--
--   This packages the tame inertial type at a place over $q$: a multiplicative system of inertia labels of exponent dividing $q^2-1$ is realised, uniquely up to replacing it by its $q$-th power (the Frobenius conjugate), by a single character of $\mathbb{F}_{q^2}^\times$, with the two extra equivalences recording when the character fails to be $\mathbb{F}_q$-valued and when it is of order dividing $q+1$. It is used in the analysis of the inertia labels attached to a newform whose associated representation is cuspidal of the relevant type at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_monoidHom_galoisField_units_forall_tameCharacter_eq_imp_eq_or_eq_pow.lean

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Mathlib.FieldTheory.Finite.GaloisField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem
ValuationSubring.exists_monoidHom_galoisField_units_forall_tameCharacter_eq_imp_eq_or_eq_pow
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {O'' : Type} [CommRing O''] [IsDomain O'']
    (a : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → O''ˣ)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, a (σ * τ) = a σ * a τ)
    (hpow : ∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q ^ 2 - 1) = 1) :
    ∃ θ : (GaloisField q 2)ˣ →* O''ˣ,
      (∀ (π : AlgebraicClosure ℚ), π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ) →
        ∀ ι : GaloisField q 2 →+* IsLocalRing.ResidueField P,
          (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
              ι (α : GaloisField q 2) = P.tameCharacter π σ → a σ = θ α) ∨
          (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ α : (GaloisField q 2)ˣ,
              ι (α : GaloisField q 2) = P.tameCharacter π σ → a σ = θ (α ^ q))) ∧
      ((∃ τ ∈ P.inertiaSubgroupIn ℚ, a τ ^ (q - 1) ≠ 1) ↔ θ ^ q ≠ θ) ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ, a σ ^ (q + 1) = 1) ↔ θ ^ (q + 1) = 1) := by sorry
