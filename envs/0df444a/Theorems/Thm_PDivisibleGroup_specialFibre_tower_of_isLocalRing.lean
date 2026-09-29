-- Prove2me | Theorems.Thm_PDivisibleGroup_specialFibre_tower_of_isLocalRing
-- name    : PDivisibleGroup.specialFibre_tower_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/3c8d7003-b789-5c76-81a9-b604e75d400c
-- title:
--   Special fibre of an explicit p-divisible tower stays local
-- statement:
--   Let $\mathcal O$ be a commutative ring, $p$ a prime, and suppose $p$ is a non-zero-divisor in $\mathcal O$, that $\mathcal O$ carries an algebra structure over $\mathbb Z/p$ whose structure map has kernel the ideal $(p)$, and that $\mathcal O$ is $(p)$-adically complete. Let $h_0$ be a natural number and $R_0 : \mathbb N \to \mathrm{Type}$ a family of commutative rings, each a cocommutative Hopf $\mathcal O$-algebra which is finite and free as an $\mathcal O$-module, equipped with bialgebra maps $t_0(v) : R_0(v+1) \to R_0(v)$ that are surjective, with $\operatorname{rank}_{\mathcal O} R_0(v) = p^{v h_0}$, with $\ker t_0(v)$ equal to the $p^v$-torsion ideal of $R_0(v+1)$ over $\mathcal O$ — the image, under the $p^v$-th convolution power of the identity algebra endomorphism, of the augmentation ideal $\ker \varepsilon$ — and with each $R_0(v)$ a local ring. The conclusion is the conjunction of four assertions about the base changes $\mathbb Z/p \otimes_{\mathcal O} R_0(v)$: the map $\mathrm{id} \otimes t_0(v)$ is surjective; $\dim_{\mathbb Z/p} \bigl(\mathbb Z/p \otimes_{\mathcal O} R_0(v)\bigr) = p^{v h_0}$; the kernel of the base-changed bialgebra map is the $p^v$-torsion ideal of $\mathbb Z/p \otimes_{\mathcal O} R_0(v+1)$ over $\mathbb Z/p$; and each $\mathbb Z/p \otimes_{\mathcal O} R_0(v)$ is a local ring.
--
--   This is the base-change (special fibre) step for $p$-divisible groups, presented not for the structure [`PDivisibleGroup`](def/PDivisibleGroup_Basic.html#L199) itself but for a tower given by its constituent data: it says that reducing a connected height-$h_0$ tower over $\mathcal O$ modulo $p$ yields a connected height-$h_0$ tower over $\mathbb Z/p$ in the same explicit currency. It feeds the analysis of formal coordinates on the special fibre, being cited by [`PDivisibleGroup.exists_mvPolynomial_specialFibre_coordinates_of_isLocalRing`](thm.html#PDivisibleGroup.exists_mvPolynomial_specialFibre_coordinates_of_isLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_specialFibre_tower_of_isLocalRing.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

universe u v

theorem PDivisibleGroup.specialFibre_tower_of_isLocalRing
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (h₀ : ℕ) (R₀ : ℕ → Type v) [∀ v, CommRing (R₀ v)] [∀ v, HopfAlgebra 𝓞 (R₀ v)]
    [∀ v, Coalgebra.IsCocomm 𝓞 (R₀ v)] [∀ v, Module.Free 𝓞 (R₀ v)] [∀ v, Module.Finite 𝓞 (R₀ v)]
    (t₀ : ∀ v, R₀ (v + 1) →ₐc[𝓞] R₀ v) (ht₀ : ∀ v, Function.Surjective (t₀ v))
    (hrank₀ : ∀ v, Module.finrank 𝓞 (R₀ v) = p ^ (v * h₀))
    (hker₀ : ∀ v, RingHom.ker (t₀ v) = PDivisibleGroup.Hopf.torsionIdeal 𝓞 (R₀ (v + 1)) (p ^ v))
    (hconn : ∀ v, IsLocalRing (R₀ v)) :
    (∀ v, Function.Surjective
        (Algebra.TensorProduct.map (AlgHom.id (ZMod p) (ZMod p)) (t₀ v : R₀ (v + 1) →ₐ[𝓞] R₀ v))) ∧
    (∀ v, Module.finrank (ZMod p) (ZMod p ⊗[𝓞] R₀ v) = p ^ (v * h₀)) ∧
    (∀ v, RingHom.ker (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (t₀ v)) =
      PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (ZMod p ⊗[𝓞] R₀ (v + 1)) (p ^ v)) ∧
    (∀ v, IsLocalRing (ZMod p ⊗[𝓞] R₀ v)) := by sorry
