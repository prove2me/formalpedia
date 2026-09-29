-- Prove2me | Theorems.Thm_SetLike_GradedMonoid_rank_le_of_eq_bot_of_kunneth_injective
-- name    : SetLike.GradedMonoid.rank_le_of_eq_bot_of_kunneth_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/d68a3398-2d86-57d7-a6b1-def108e11725
-- title:
--   Degree-one rank bound from an injective Künneth map
-- statement:
--   Let $k$ be a field and let $H$, $H'$ be rings equipped with $k$-algebra structures. Let $\mathcal A : \mathbb N \to \mathrm{Submodule}\,k\,H$ be a family of $k$-subspaces of $H$ which is a graded monoid in the sense that $1 \in \mathcal A_0$ and $\mathcal A_a \cdot \mathcal A_b \subseteq \mathcal A_{a+b}$, and let $p_1, p_2, m : H \to H'$ be $k$-algebra homomorphisms. Assume: (i) the $k$-linear map $\bigoplus_{(a,b) \in \mathbb N \times \mathbb N} \mathcal A_a \otimes_k \mathcal A_b \to H'$ whose $(a,b)$-component sends $u \otimes v$ to $p_1(u)\,p_2(v)$ (that is, the multiplication map of $H'$ composed with the tensor product of $p_1$ restricted to $\mathcal A_a$ and $p_2$ restricted to $\mathcal A_b$) is injective; (ii) $p_2(x)\,p_1(y) = -\,p_1(y)\,p_2(x)$ for all $x, y \in \mathcal A_1$; (iii) $m(x) = p_1(x) + p_2(x)$ for all $x \in \mathcal A_1$. If $d$ is a natural number with $\mathcal A_{d+1} = 0$, then the rank of $\mathcal A_1$ as a $k$-vector space, as a cardinal, is at most $d$; in particular $\mathcal A_1$ is finite-dimensional.
--
--   This is the dimension bound half of the structure lemma used to compute the coherent cohomology of an abelian variety: a graded algebra whose degree-one elements are primitive for a coproduct-like map and which vanishes in degree $d+1$ has degree-one part of dimension at most $d$, stated here with only the algebraic structure the argument needs. It is used in the computation of the Čech rank of the unit component in characteristic $p$ and in the companion statement describing the degree-two part when $\dim \mathcal A_1 = 2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_SetLike_GradedMonoid_rank_le_of_eq_bot_of_kunneth_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct DirectSum

universe u

theorem SetLike.GradedMonoid.rank_le_of_eq_bot_of_kunneth_injective
    {k : Type u} [Field k] {H : Type u} [Ring H] [Algebra k H]
    {H' : Type u} [Ring H'] [Algebra k H']
    (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜] (p₁ p₂ m : H →ₐ[k] H')
    (hK : Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)))
    (hanti : ∀ x ∈ 𝒜 1, ∀ y ∈ 𝒜 1, p₂ x * p₁ y = -(p₁ y * p₂ x))
    (hm : ∀ x ∈ 𝒜 1, m x = p₁ x + p₂ x)
    {d : ℕ} (hd : 𝒜 (d + 1) = ⊥) :
    Module.rank k ↥(𝒜 1) ≤ d := by sorry
