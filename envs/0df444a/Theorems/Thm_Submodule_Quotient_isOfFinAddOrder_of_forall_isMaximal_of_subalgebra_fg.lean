-- Prove2me | Theorems.Thm_Submodule_Quotient_isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg
-- name    : Submodule.Quotient.isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/572e4f15-30c8-5042-9766-e7c3dad80a01
-- title:
--   Local torsion above I forces torsion in J/γ J
-- statement:
--   Let $R$ be a commutative ring and $J$ an additive abelian group carrying an $R$-module structure, and let $\rho : R \to \operatorname{End}_{\mathbb Z}(J)$ be a ring homomorphism which induces that structure, in the sense that $t \cdot x = \rho(t)(x)$ for all $t \in R$ and $x \in J$. Assume given a $\mathbb Z$-subalgebra $S \subseteq \operatorname{End}_{\mathbb Z}(J)$ whose underlying $\mathbb Z$-submodule is finitely generated and which contains $\rho(t)$ for every $t \in R$. Let $I$ and $\gamma$ be ideals of $R$ such that $\gamma$ contains every $t \in R$ for which there exists $i \in I$ with $((1+i)t) \cdot x = 0$ for all $x \in J$. Let $z$ be an element of the quotient $J / (\gamma \cdot \top)$, where $\gamma \cdot \top$ is the submodule $\gamma J$ obtained by acting with the ideal $\gamma$ on the whole of $J$. Suppose that for every maximal ideal $\mathfrak m$ of $R$ containing $I$ there is some $s \in R \setminus \mathfrak m$ with $s \cdot z$ of finite additive order. Then $z$ itself has finite additive order.
--
--   This is the abstract support argument underlying Mazur's treatment of rational torsion on the Eisenstein quotient, with $R$ the Hecke algebra, $I$ the Eisenstein ideal, $\gamma$ the associated kernel ideal and $J/\gamma J$ the Eisenstein quotient: torsion at every maximal ideal above $I$, in the localised sense above, implies torsion. It is used in the proof that the rational points of the Eisenstein quotient form a torsion subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_Quotient_isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise

theorem Submodule.Quotient.isOfFinAddOrder_of_forall_isMaximal_of_subalgebra_fg
    {R J : Type*} [CommRing R] [AddCommGroup J] [Module R J]
    (ρ : R →+* Module.End ℤ J) (hρ : ∀ (t : R) (x : J), t • x = ρ t x)
    (S : Subalgebra ℤ (Module.End ℤ J)) (hS : (Subalgebra.toSubmodule S).FG)
    (hρS : ∀ t, ρ t ∈ S)
    (I γ : Ideal R) (hγ : ∀ t : R, (∃ i ∈ I, ∀ x : J, ((1 + i) * t) • x = 0) → t ∈ γ)
    (z : J ⧸ (γ • (⊤ : Submodule R J)))
    (hz : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → I ≤ 𝔪 → ∃ s ∉ 𝔪, IsOfFinAddOrder (s • z)) :
    IsOfFinAddOrder z := by sorry
