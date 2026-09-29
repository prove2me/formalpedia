-- Prove2me | Theorems.Thm_PDivisibleGroup_exists_connectedComponent_tower_of_isLocalRing_cartierDual
-- name    : PDivisibleGroup.exists_connectedComponent_tower_of_isLocalRing_cartierDual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/3c832669-6361-5b68-a3f8-dbc2edc1314a
-- title:
--   Connected components of a unipotent p-divisible tower
-- statement:
--   Let $\mathcal O$ be a commutative ring and $p$ a prime such that $p$ is a non-zero-divisor in $\mathcal O$, such that $\mathbb Z/p$ is an $\mathcal O$-algebra whose structure map has kernel exactly the ideal $(p)$, and such that $\mathcal O$ is adically complete for $(p)$. Let $h\in\mathbb N$ and let $L_0,L_1,\dots$ be commutative rings, each a cocommutative Hopf $\mathcal O$-algebra which is finite and free as an $\mathcal O$-module, equipped with bialgebra maps $t_v\colon L_{v+1}\to L_v$ which are surjective, with $\operatorname{finrank}_{\mathcal O}L_v=p^{vh}$ and with $\ker t_v$ equal to the $p^v$-torsion ideal of $L_{v+1}$, i.e. the image of the augmentation ideal $\ker(\varepsilon)$ under the algebra endomorphism [`PDivisibleGroup.Hopf.nsmulAlgHom`](def/PDivisibleGroup_Basic.html#L16) attached to $p^v$ (the $p^v$-fold convolution power of the identity). Assume further that for every $v$ the Cartier dual $\operatorname{Hom}_{\mathbb Z/p}((\mathbb Z/p)\otimes_{\mathcal O}L_v,\mathbb Z/p)$, with its [`CartierDual`](def/HopfAlgebra_CartierDual.html#L12) ring structure, is a local ring. Then there exist $h_0\le h$ and rings $R_{0,v}$ ($v\in\mathbb N$), each carrying commutative ring, cocommutative Hopf $\mathcal O$-algebra, free and finite module structures, bialgebra maps $\rho_v\colon L_v\to R_{0,v}$ and $t_{0,v}\colon R_{0,v+1}\to R_{0,v}$, and elements $e_v\in L_v$, such that every $t_{0,v}$ is surjective, $\operatorname{finrank}_{\mathcal O}R_{0,v}=p^{vh_0}$, $\ker t_{0,v}$ is the $p^v$-torsion ideal of $R_{0,v+1}$ in the same sense, $\rho_v\circ t_v=t_{0,v}\circ\rho_{v+1}$, and for each $v$: $e_v$ is idempotent with $\varepsilon(e_v)=1$, $\rho_v$ is surjective with kernel (as a map of algebras) the ideal $(1-e_v)$, and $R_{0,v}$, $(\mathbb Z/p)\otimes_{\mathcal O}R_{0,v}$ and the Cartier dual of the latter are all local rings.
--
--   This is the statement that passing to connected components preserves $p$-divisibility: the connected–étale decomposition of each level of a $p$-divisible group over a $p$-adically complete base with residue ring $\mathbb Z/p$ assembles into a sub-tower $\Gamma^0$ of height $h_0\le h$, cut out levelwise by idempotents with $\varepsilon(e_v)=1$. The input data are exactly the fields of the structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199) (here given unbundled, together with levelwise unipotence), and the output is data of the same shape; it feeds the passage from such a tower to a multivariate formal group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_exists_connectedComponent_tower_of_isLocalRing_cartierDual.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_HopfAlgebra_CartierDual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem PDivisibleGroup.exists_connectedComponent_tower_of_isLocalRing_cartierDual
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h : ℕ) (L : ℕ → Type v) [∀ v, CommRing (L v)] [∀ v, HopfAlgebra 𝓞 (L v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (L v)] [∀ v, Module.Free 𝓞 (L v)] [∀ v, Module.Finite 𝓞 (L v)]
    (t : ∀ v, L (v + 1) →ₐc[𝓞] L v) (ht : ∀ v, Function.Surjective (t v))
    (hrankL : ∀ v, Module.finrank 𝓞 (L v) = p ^ (v * h))
    (hkerL : ∀ v, RingHom.ker (t v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (L (v + 1)) (p ^ v))
    (hunipL : ∀ v, IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (L v)))) :
    ∃ (h₀ : ℕ) (_ : h₀ ≤ h)
      (R₀ : ℕ → Type v) (_ : ∀ v, CommRing (R₀ v)) (_ : ∀ v, HopfAlgebra 𝓞 (R₀ v))
      (_ : ∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)) (_ : ∀ v, Module.Free 𝓞 (R₀ v))
      (_ : ∀ v, Module.Finite 𝓞 (R₀ v))
      (ρ : ∀ v, L v →ₐc[𝓞] R₀ v) (e : ∀ v, L v) (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v),
    (∀ v, Function.Surjective (t₀ v)) ∧
    (∀ v, Module.finrank 𝓞 (R₀ v) = p ^ (v * h₀)) ∧
    (∀ v, RingHom.ker (t₀ v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (R₀ (v + 1)) (p ^ v)) ∧
    (∀ v, (ρ v).comp (t v) = (t₀ v).comp (ρ (v + 1))) ∧
    ∀ v, IsIdempotentElem (e v) ∧ Coalgebra.counit (R := 𝓞) (e v) = 1 ∧
      Function.Surjective (ρ v) ∧ RingHom.ker (ρ v : L v →ₐ[𝓞] R₀ v) = Ideal.span {1 - e v} ∧
      IsLocalRing (R₀ v) ∧ IsLocalRing (TensorProduct 𝓞 (ZMod p) (R₀ v)) ∧
      IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) (R₀ v))) := by sorry
