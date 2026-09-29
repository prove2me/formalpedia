-- Prove2me | Theorems.Thm_SetLike_GradedMonoid_exists_forall_mem_two_eq_smul_mul_of_finrank_two_add_one_eq_of_kunneth_injective
-- name    : SetLike.GradedMonoid.exists_forall_mem_two_eq_smul_mul_of_finrank_two_add_one_eq_of_kunneth_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/cc03e279-c950-5398-805e-3b91161406aa
-- title:
--   Degree two spanned by one product of degree-one elements
-- statement:
--   Let $k$ be a field and let $H$, $H'$ be $k$-algebras (rings with a $k$-algebra structure, all three types in the same universe). Let $\mathcal A \colon \mathbb N \to \mathrm{Submodule}_k(H)$ be a family of $k$-submodules of $H$ forming a graded monoid, so $1 \in \mathcal A_0$ and $\mathcal A_a \cdot \mathcal A_b \subseteq \mathcal A_{a+b}$, and let $p_1, p_2, m \colon H \to H'$ be $k$-algebra homomorphisms. Assume: (i) the map $\bigoplus_{(a,b) \in \mathbb N \times \mathbb N} \mathcal A_a \otimes_k \mathcal A_b \to H'$ whose $(a,b)$-component sends $u \otimes v$ to $p_1(u)\,p_2(v)$ is injective; (ii) $p_2(x)\,p_1(y) = -\,p_1(y)\,p_2(x)$ for all $x, y \in \mathcal A_1$; (iii) $m(x) = p_1(x) + p_2(x)$ for all $x \in \mathcal A_1$; (iv) $\mathcal A_3 = 0$; and (v) $\mathcal A_2$ is a finite $k$-module with $\dim_k \mathcal A_2 + 1 = \dim_k \mathcal A_1$. The conclusion is that there exist $a, b \in \mathcal A_1$ such that every $x \in \mathcal A_2$ is of the form $c \cdot (ab)$ for some scalar $c \in k$; that is, $\mathcal A_2$ is contained in the line $k \cdot ab$.
--
--   This is the degree-two bookkeeping for a graded cohomology algebra with an injective Künneth-type multiplication map and primitive degree-one part: under the numerical hypothesis $\dim \mathcal A_2 + 1 = \dim \mathcal A_1$ and vanishing in degree three, the whole of $\mathcal A_2$ lies on a single line spanned by a product of two degree-one classes. It is used in the analysis of cohomology of abelian schemes of relative dimension related to topological Krull dimension two, where it supplies the exactness step for degree-two classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_SetLike_GradedMonoid_exists_forall_mem_two_eq_smul_mul_of_finrank_two_add_one_eq_of_kunneth_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct DirectSum

universe u

theorem SetLike.GradedMonoid.exists_forall_mem_two_eq_smul_mul_of_finrank_two_add_one_eq_of_kunneth_injective
    {k : Type u} [Field k] {H : Type u} [Ring H] [Algebra k H]
    {H' : Type u} [Ring H'] [Algebra k H']
    (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] (p₁ p₂ m : H →ₐ[k] H')
    (hK : Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)))
    (hanti : ∀ x ∈ 𝒜 1, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = -(p₁ y * p₂ x))
    (hm : ∀ x ∈ 𝒜 1, m x = p₁ x + p₂ x)
    (h3 : 𝒜 3 = ⊥) [Module.Finite k ↥(𝒜 2)]
    (hdim : Module.finrank k ↥(𝒜 2) + 1 = Module.finrank k ↥(𝒜 1)) :
    ∃ a ∈ 𝒜 1, ∃ b ∈ 𝒜 1, ∀ x ∈ 𝒜 2, ∃ c : k, x = c • (a * b) := by sorry
