-- Prove2me | Theorems.Thm_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_inertia_diagonal_of_swap
-- name    : ResidualGaloisRep.forall_decompositionStable_eq_bot_or_top_of_inertia_diagonal_of_swap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/7de870e8-5ec2-59b7-889c-12c1bc105959
-- title:
--   Decomposition-stable submodules are trivial for swapped diagonal inertia
-- statement:
--   Let $k$ be a field and let $\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ of rank $2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ to $\mathrm{End}_k(V)$ which factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite over $\mathbb{Q}$, such that $\rho(\sigma) = 1$ whenever $\sigma$ fixes $L$ pointwise. Let $P$ be a valuation subring of $\overline{\mathbb{Q}}$, and write $I_P$ for the image in the full Galois group of the inertia subgroup of $P$ over $\mathbb{Q}$ (taken inside, and pushed forward along the inclusion of, the decomposition subgroup $D_P$ of $P$ over $\mathbb{Q}$). Assume: there exist a field $k'$, a ring homomorphism $\psi_k : k \to k'$, a basis $b_0, b_1$ of the base change $k' \otimes_k V$ (with Galois action obtained by base-changing each $\rho(\sigma)$ along $\psi_k$), and two functions $\psi, \psi'$ from the Galois group to $k'$ — not required to be multiplicative — such that every $\sigma \in I_P$ acts by $b_0 \mapsto \psi(\sigma) b_0$ and $b_1 \mapsto \psi'(\sigma) b_1$, such that $\psi(\sigma_0) \neq \psi'(\sigma_0)$ for some $\sigma_0 \in I_P$, and such that some $\varphi_0 \in D_P$ sends $b_0$ into the line $k' b_1$. The conclusion is that for every field $k''$ and every ring homomorphism $\psi'' : k \to k''$, every $k''$-submodule of $k'' \otimes_k V$ stable under $\rho(\sigma)$ for all $\sigma \in D_P$ is either $\bot$ or $\top$.
--
--   This is the linear-algebra criterion underlying the supersingular case of the local analysis at $p$: the two inertia eigenlines are the only lines that can be inertia-stable once $\psi$ and $\psi'$ separate some inertia element, and an element of the decomposition group interchanging them leaves no proper stable subspace, the conclusion being asserted after an arbitrary further extension of the coefficient field. It is used in [`CuspForm.point_residual_stable_eq_bot_or_top_of_not_isUnit_heckeT_of_ne_two`](thm.html#CuspForm.point_residual_stable_eq_bot_or_top_of_not_isUnit_heckeT_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_forall_decompositionStable_eq_bot_or_top_of_inertia_diagonal_of_swap.lean

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ResidualGaloisRep.forall_decompositionStable_eq_bot_or_top_of_inertia_diagonal_of_swap
    {k : Type} [Field k] (ρ : ResidualGaloisRep k)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (h : ∃ (k' : Type) (_ : Field k') (ψk : k →+* k')
        (b : Module.Basis (Fin 2) k' (ρ.baseChangeAlong ψk).V)
        (ψ ψ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k'),
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
            (ρ.baseChangeAlong ψk).ρ σ (b 0) = ψ σ • b 0 ∧
            (ρ.baseChangeAlong ψk).ρ σ (b 1) = ψ' σ • b 1) ∧
        (∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ σ₀ ≠ ψ' σ₀) ∧
        (∃ φ₀ ∈ P.decompositionSubgroup ℚ,
            (ρ.baseChangeAlong ψk).ρ φ₀ (b 0) ∈ Submodule.span k' {b 1})) :
    ∀ (k'' : Type) [Field k''] (ψ'' : k →+* k''),
      ∀ L : Submodule k'' (ρ.baseChangeAlong ψ'').V,
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, (ρ.baseChangeAlong ψ'').ρ σ v ∈ L) →
        L = ⊥ ∨ L = ⊤ := by sorry
