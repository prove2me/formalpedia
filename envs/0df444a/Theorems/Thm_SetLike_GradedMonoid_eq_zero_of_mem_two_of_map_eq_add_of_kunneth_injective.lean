-- Prove2me | Theorems.Thm_SetLike_GradedMonoid_eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective
-- name    : SetLike.GradedMonoid.eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/d0cd817c-071f-59c3-abcc-b2178690c3c7
-- title:
--   Primitive degree-two elements vanish under an injective Künneth map
-- statement:
--   Let $k$ be a field and let $H$, $H'$ be $k$-algebras. Let $\mathcal{A} \colon \mathbb{N} \to \{k\text{-submodules of } H\}$ be a family which is a graded monoid, i.e. $1 \in \mathcal{A}_0$ and $\mathcal{A}_a \cdot \mathcal{A}_b \subseteq \mathcal{A}_{a+b}$, and let $p_1, p_2, m \colon H \to H'$ be $k$-algebra homomorphisms. Assume: (i) the Künneth-type map $\bigoplus_{(a,b) \in \mathbb{N}^2} \mathcal{A}_a \otimes_k \mathcal{A}_b \to H'$ assembled from the maps $u \otimes v \mapsto p_1(u)\,p_2(v)$ is injective; (ii) $p_2(x)p_1(y) = -p_1(y)p_2(x)$ for all $x, y \in \mathcal{A}_1$; (iii) $p_2(x)p_1(y) = p_1(y)p_2(x)$ for all $x \in \mathcal{A}_2$ and $y \in \mathcal{A}_1$; (iv) $m(y) = p_1(y) + p_2(y)$ for all $y \in \mathcal{A}_1$. Assume further that for some $d \in \mathbb{N}$ there is a $k$-linearly independent family $a_0, \dots, a_{d-1}$ of elements of $\mathcal{A}_1$, and that $\mathcal{A}_n = 0$ for every $n > d$. Then any $x \in \mathcal{A}_2$ satisfying $m(x) = p_1(x) + p_2(x)$ is zero. No nontriviality of $H$ is assumed.
--
--   This is the graded-algebra form of the classical statement that a primitive class of degree two in the cohomology ring of an abelian variety vanishes once the degree-one part has maximal dimension $d$ and the ring is concentrated in degrees $\le d$; the intended model has $H$ the Čech cohomology ring $\bigoplus_n \check{H}^n(A, \mathcal{O}_A)$ of a $d$-dimensional abelian variety, $p_1, p_2, m$ the pull-backs along the two projections and the group law, and $x$ an obstruction class that is primitive by naturality. It is used in the construction of the obstruction two-cocycle for abelian schemes and in the pull-back isomorphism statements for fake elliptic curves, and its proof invokes [`SetLike.GradedMonoid.listProd_ne_zero_of_linearIndependent_of_kunneth_injective`](thm.html#SetLike.GradedMonoid.listProd_ne_zero_of_linearIndependent_of_kunneth_injective), the nonvanishing of the product of a linearly independent family of degree-one elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_SetLike_GradedMonoid_eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct DirectSum

universe u

theorem SetLike.GradedMonoid.eq_zero_of_mem_two_of_map_eq_add_of_kunneth_injective
    {k : Type u} [Field k] {H : Type u} [Ring H] [Algebra k H]
    {H' : Type u} [Ring H'] [Algebra k H']
    (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] (p₁ p₂ m : H →ₐ[k] H')
    (hK : Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)))
    (hanti : ∀ x ∈ 𝒜 1, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = -(p₁ y * p₂ x))
    (hcomm : ∀ x ∈ 𝒜 2, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = p₁ y * p₂ x)
    (hm : ∀ y ∈ 𝒜 1, m y = p₁ y + p₂ y)
    {d : ℕ} (a : Fin d → H) (ha : ∀ i, a i ∈ 𝒜 1) (hli : LinearIndependent k a)
    (hd : ∀ n : ℕ, d < n → 𝒜 n = ⊥)
    (x : H) (hx : x ∈ 𝒜 2) (hmx : m x = p₁ x + p₂ x) :
    x = 0 := by sorry
