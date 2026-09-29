-- Prove2me | Theorems.Thm_ResidualGaloisRep_exists_eq_smul_one_of_forall_mul_eq_smul_mul
-- name    : ResidualGaloisRep.exists_eq_smul_one_of_forall_mul_eq_smul_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/c6dfe1e3-62f8-58a4-9cd1-4687ffbda3b3
-- title:
--   Intertwiners between ρ̄ and its twist ρ̄⊗χ are scalar
-- statement:
--   Let $k$ be a field in which $2 \neq 0$, and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\mathrm{End}_k(V)$, such that $\rho$ factors through a finite level, i.e. some intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ with $[L:\mathbb Q]$ finite has $\rho(\sigma) = 1$ for every $\sigma$ fixing $L$ pointwise. Assume: (i) $\bar\rho$ is absolutely irreducible, meaning that in the base change of $\bar\rho$ to $\overline{k}$ the only $\overline{k}$-submodules of $\overline{k} \otimes_k V$ stable under all $\rho(\sigma)$ are $\bot$ and $\top$; and (ii) for every field $K$ that is a $k$-algebra and every subgroup $G \leq \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of index $2$, every $K$-submodule of $K \otimes_k V$ stable under the base-changed operators $\rho(\sigma)$ for $\sigma \in G$ is $\bot$ or $\top$. Let $\chi \colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to k^{\times}$ be a monoid homomorphism and $Y \in \mathrm{End}_k(V)$ satisfy $Y \cdot \rho(\sigma) = \chi(\sigma)\,(\rho(\sigma) \cdot Y)$ in $\mathrm{End}_k(V)$ for all $\sigma$. Then there is $c \in k$ with $Y = c \cdot \mathrm{id}_V$, and $c = 0$ whenever $\chi$ is not the trivial homomorphism.
--
--   This is the twist-rigidity form of Schur's lemma for a two-dimensional residual representation: $\mathrm{Hom}(\bar\rho, \bar\rho)$ consists of scalars, and $\mathrm{Hom}(\bar\rho, \bar\rho \otimes \chi) = 0$ for $\chi \neq 1$, under the hypothesis that absolute irreducibility persists on index-two subgroups. It is used in the bound on the rank of the strict Selmer group in terms of the number of Taylor–Wiles primes and the rank of the dual Selmer group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_exists_eq_smul_one_of_forall_mul_eq_smul_mul.lean

import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ResidualGaloisRep.exists_eq_smul_one_of_forall_mul_eq_smul_mul
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* kˣ)
    (Y : Module.End k ρbar.V)
    (hY : ∀ σ, Y * ρbar.ρ σ = ((χ σ : kˣ) : k) • (ρbar.ρ σ * Y)) :
    ∃ c : k, Y = c • (1 : Module.End k ρbar.V) ∧ (χ ≠ 1 → c = 0) := by sorry
