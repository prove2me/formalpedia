-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_inertia_diagonal_swap_of_eigenvector
-- name    : ResidualGaloisRep.exists_inertia_diagonal_swap_of_eigenvector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/e0faa692-7766-5e8f-ab01-d38a07a35349
-- title:
--   Diagonalising inertia with a swap from a moved eigencharacter
-- statement:
--   Let $k$ be a field and let $\rho$ be a residual Galois representation over $k$, i.e. a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\rho \colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{End}_k(V)$ that is trivial on the subgroup fixing some finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ pointwise; let $P$ be a valuation subring of $\overline{\mathbb{Q}}$, and write $I_P$ for the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ (a subgroup of the decomposition subgroup $D_P$ of $P$, transported along the inclusion $D_P \hookrightarrow \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$). Assume there exist a field $k'$ and a ring homomorphism $\psi_k \colon k \to k'$, a nonzero vector $v$ in the base change $k' \otimes_k V$ (carrying the base-changed action), and an arbitrary function $\chi$ on $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with values in $k'$, such that every $\sigma \in I_P$ acts on $v$ by the scalar $\chi(\sigma)$, and such that $\chi(\varphi^{-1}\sigma_0\varphi) \neq \chi(\sigma_0)$ for some $\varphi \in D_P$ and some $\sigma_0 \in I_P$. Then there exist a field $k'$, a ring homomorphism $\psi_k \colon k \to k'$, a basis $b_0, b_1$ of $k' \otimes_k V$ indexed by $\mathrm{Fin}\,2$, and functions $\psi, \psi'$ on $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with values in $k'$, such that each $\sigma \in I_P$ sends $b_0$ to $\psi(\sigma) b_0$ and $b_1$ to $\psi'(\sigma) b_1$, such that $\psi(\sigma_0) \neq \psi'(\sigma_0)$ for some $\sigma_0 \in I_P$, and such that $\varphi_0 \cdot b_0$ lies in the line $k' b_1$ for some $\varphi_0 \in D_P$.
--
--   This is the linear-algebra step producing, from a single inertia eigenvector whose eigencharacter is not stable under conjugation by the decomposition group, the configuration in which inertia acts diagonally in a basis and a Frobenius-type element interchanges the two lines. It supplies exactly the hypothesis block used in the analysis of residually stable subspaces, and is cited in the proof of [`CuspForm.point_residual_stable_eq_bot_or_top_of_not_isUnit_heckeT_of_ne_two`](thm.html#CuspForm.point_residual_stable_eq_bot_or_top_of_not_isUnit_heckeT_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_inertia_diagonal_swap_of_eigenvector.lean

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ResidualGaloisRep.exists_inertia_diagonal_swap_of_eigenvector
    {k : Type} [Field k] (ρ : ResidualGaloisRep k)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (h : ∃ (k' : Type) (_ : Field k') (ψk : k →+* k') (v : (ρ.baseChangeAlong ψk).V)
        (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k'),
        v ≠ 0 ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, (ρ.baseChangeAlong ψk).ρ σ v = χ σ • v) ∧
        (∃ φ ∈ P.decompositionSubgroup ℚ, ∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, χ (φ⁻¹ * σ₀ * φ) ≠ χ σ₀)) :
    ∃ (k' : Type) (_ : Field k') (ψk : k →+* k')
        (b : Module.Basis (Fin 2) k' (ρ.baseChangeAlong ψk).V)
        (ψ ψ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → k'),
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
            (ρ.baseChangeAlong ψk).ρ σ (b 0) = ψ σ • b 0 ∧
            (ρ.baseChangeAlong ψk).ρ σ (b 1) = ψ' σ • b 1) ∧
        (∃ σ₀ ∈ P.inertiaSubgroupIn ℚ, ψ σ₀ ≠ ψ' σ₀) ∧
        (∃ φ₀ ∈ P.decompositionSubgroup ℚ,
            (ρ.baseChangeAlong ψk).ρ φ₀ (b 0) ∈ Submodule.span k' {b 1}) := by sorry
