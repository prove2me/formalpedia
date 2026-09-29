-- Prove2me | Theorems.Thm_ResidualGaloisRep_eq_zero_of_forall_map_adZeroRep_eq_smul
-- name    : ResidualGaloisRep.eq_zero_of_forall_map_adZeroRep_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/271e980f-1f10-5061-85f0-b2371185f709
-- title:
--   No nonzero χ-equivariant functional on ad⁰ρ̄
-- statement:
--   Let $k$ be a field in which $2 \neq 0$ and let $\bar\rho$ be a residual Galois representation over $k$, that is: a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_k(V)$ which factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that $\rho(\sigma) = 1$ whenever $\sigma$ fixes $L$ pointwise. Assume: (i) $\bar\rho$ is absolutely irreducible, meaning that in $\overline{k} \otimes_k V$, with $\sigma$ acting by the base change of $\rho(\sigma)$, the only submodules stable under all $\sigma$ are $\bot$ and $\top$; (ii) for every field $K$ that is a $k$-algebra and every subgroup $G$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of index $2$, the only $K$-submodules of $K \otimes_k V$ stable under the base changes of $\rho(\sigma)$ for $\sigma \in G$ are $\bot$ and $\top$. Let $\chi$ be any monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $k^\times$ (no continuity or finite-level condition is imposed), and let $\varphi$ be a $k$-linear functional on the kernel of the trace form on $\mathrm{End}_k(V)$ satisfying $\varphi(\rho(\sigma) f \rho(\sigma^{-1})) = \chi(\sigma)\,\varphi(f)$ for all $\sigma$ and all trace-zero $f$. Then $\varphi = 0$.
--
--   In classical terms this is the vanishing $\mathrm{Hom}_{\mathbb{Q}}(\mathrm{ad}^0\bar\rho, k(\chi)) = 0$, equivalently $H^0(\mathbb{Q}, (\mathrm{ad}^0\bar\rho)^{\vee}(\chi)) = 0$, under absolute irreducibility of $\bar\rho$ together with irreducibility after restriction to every index-two subgroup; the case where $\chi$ is the mod $p$ cyclotomic character gives $H^0(\mathbb{Q}, \mathrm{ad}^0\bar\rho(1)) = 0$. It is used in the construction of Taylor–Wiles primes, being cited by [`ResidualGaloisRep.exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero`](thm.html#ResidualGaloisRep.exists_apply_eq_self_and_adZeroRep_eq_one_and_cocycles_apply_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_eq_zero_of_forall_map_adZeroRep_eq_smul.lean

import Definitions.Def_GaloisRep_AdZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ResidualGaloisRep.eq_zero_of_forall_map_adZeroRep_eq_smul
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hTW : ∀ (K : Type) [Field K] [Algebra k K]
      (G : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)), G.index = 2 →
      ∀ V : Submodule K (ρbar.baseChange K).V,
        (∀ σ ∈ G, ∀ x ∈ V, (ρbar.baseChange K).ρ σ x ∈ V) → V = ⊥ ∨ V = ⊤)
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* kˣ)
    (φ : LinearMap.ker (LinearMap.trace k ρbar.V) →ₗ[k] k)
    (hφ : ∀ σ f, φ (ρbar.adZeroRep σ f) = ((χ σ : kˣ) : k) • φ f) :
    φ = 0 := by sorry
