-- Prove2me | Theorems.Thm_PDivisibleGroup_finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub
-- name    : PDivisibleGroup.finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/79324088-b03f-5eff-980b-4ce1270df9e0
-- title:
--   Rank of the connected component multiplies along [p]
-- statement:
--   Let $\mathcal O$ be a local commutative ring, $p$ a prime and $h$ a natural number. Let $L : \mathbb N \to \mathrm{Type}$ be a family of commutative, cocommutative Hopf $\mathcal O$-algebras, each finite and free as an $\mathcal O$-module, equipped with bialgebra maps $t_v : L(v+1) \to L(v)$ that are surjective, such that $\operatorname{finrank}_{\mathcal O} L(v) = p^{vh}$ for all $v$ and such that $\ker t_v$ is the $p^v$-torsion ideal of $L(v+1)$, namely the image of the augmentation ideal $\ker(\varepsilon)$ under the algebra endomorphism $[p^v]$ of $L(v+1)$ given by the $p^v$-th convolution power of the identity. Fix $v$, and let $R_1$, $R_0$ be commutative Hopf $\mathcal O$-algebras, finite free over $\mathcal O$ and local rings, together with surjective bialgebra maps $\rho_1 : L(v+1) \to R_1$ and $\rho_0 : L(v) \to R_0$, and idempotents $e_1 \in L(v+1)$, $e_0 \in L(v)$ with $\varepsilon(e_1) = \varepsilon(e_0) = 1$, such that $\ker \rho_1 = (1-e_1)$ and $\ker \rho_0 = (1-e_0)$. Then the quotient of $R_1$ by its $p$-torsion ideal, the image of $\ker(\varepsilon)$ under the $p$-th convolution power $[p]$ of the identity of $R_1$, is a free $\mathcal O$-module, and $\operatorname{finrank}_{\mathcal O} R_1 = \operatorname{finrank}_{\mathcal O}\bigl(R_1/[p]^{*}\ker(\varepsilon)\bigr) \cdot \operatorname{finrank}_{\mathcal O} R_0$.
--
--   In the geometric reading, $R_1$ and $R_0$ are the coordinate rings of the connected components $\Gamma^0_{v+1}$ and $\Gamma^0_v$ of two consecutive levels of a $p$-divisible group of height $h$ over $\mathcal O$, cut out by the unit idempotents, and the conclusion is the multiplicativity of orders $|\Gamma^0_{v+1}| = |\Gamma^0_{v+1}[p]|\cdot|\Gamma^0_v|$ expressing that multiplication by $p$ carries $\Gamma^0_{v+1}$ onto $\Gamma^0_v$ with kernel $\Gamma^0_{v+1}[p]$. It is used in [`PDivisibleGroup.exists_connectedComponent_tower_of_isLocalRing_cartierDual`](thm.html#PDivisibleGroup.exists_connectedComponent_tower_of_isLocalRing_cartierDual), in the construction of the connected part of a $p$-divisible group as again a $p$-divisible group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w w'

theorem PDivisibleGroup.finrank_connectedComponent_succ_eq_mul_of_ker_eq_span_one_sub
    (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] (p : ℕ) [Fact p.Prime] (h : ℕ)
    (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (v : ℕ)
    (R₁ : Type w) [CommRing R₁] [HopfAlgebra 𝓞 R₁] [Module.Free 𝓞 R₁] [Module.Finite 𝓞 R₁]
    (ρ₁ : L (v + 1) →ₐc[𝓞] R₁) (e₁ : L (v + 1)) (he₁ : IsIdempotentElem e₁)
    (hε₁ : Coalgebra.counit (R := 𝓞) e₁ = 1) (hρ₁ : Function.Surjective ρ₁)
    (hk₁ : RingHom.ker (ρ₁ : L (v + 1) →ₐ[𝓞] R₁) = Ideal.span {1 - e₁}) (hR₁ : IsLocalRing R₁)
    (R₀ : Type w') [CommRing R₀] [HopfAlgebra 𝓞 R₀] [Module.Free 𝓞 R₀] [Module.Finite 𝓞 R₀]
    (ρ₀ : L v →ₐc[𝓞] R₀) (e₀ : L v) (he₀ : IsIdempotentElem e₀)
    (hε₀ : Coalgebra.counit (R := 𝓞) e₀ = 1) (hρ₀ : Function.Surjective ρ₀)
    (hk₀ : RingHom.ker (ρ₀ : L v →ₐ[𝓞] R₀) = Ideal.span {1 - e₀}) (hR₀ : IsLocalRing R₀) :
    Module.Free 𝓞 (R₁ ⧸ PDivisibleGroup.Hopf.torsionIdeal 𝓞 R₁ p) ∧
      Module.finrank 𝓞 R₁ =
        Module.finrank 𝓞 (R₁ ⧸ PDivisibleGroup.Hopf.torsionIdeal 𝓞 R₁ p) * Module.finrank 𝓞 R₀ := by sorry
