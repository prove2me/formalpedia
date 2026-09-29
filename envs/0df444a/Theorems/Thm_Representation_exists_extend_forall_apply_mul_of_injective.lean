-- Prove2me | Theorems.Thm_Representation_exists_extend_forall_apply_mul_of_injective
-- name    : Representation.exists_extend_forall_apply_mul_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/bd19b1b4-2891-560c-ad60-8f41dfa4b07c
-- title:
--   Extension of right-translation-equivariant maps into ℂ^G
-- statement:
--   Let $H$ and $G$ be groups, let $W$ be a complex vector space, and let $\iota : H \to G$ be an injective group homomorphism. Let $\rho$ be a representation of $H$ on $W$ over $\mathbb{C}$, and let $P \subseteq W$ be a $\mathbb{C}$-subspace which is stable under $\rho$, in the sense that $\rho(k)v \in P$ for every $k \in H$ and every $v \in P$. Let $T : P \to (G \to \mathbb{C})$ be a $\mathbb{C}$-linear map into the space of all complex-valued functions on $G$, and assume that $T$ intertwines $\rho$ with right translation along $\iota$: for all $k \in H$, $v \in P$ and $x \in G$, the value of $T$ at the element $\rho(k)v$ of $P$ evaluated at $x$ equals $T(v)(x\,\iota(k))$. The conclusion asserts the existence of a $\mathbb{C}$-linear map $T' : W \to (G \to \mathbb{C})$ satisfying the same equivariance on all of $W$, namely $T'(\rho(k)v)(x) = T'(v)(x\,\iota(k))$ for all $k \in H$, $v \in W$, $x \in G$, and restricting to $T$ on $P$, i.e. $T'(v) = T(v)$ for every $v \in P$.
--
--   This is the injectivity of the module $\mathbb{C}^G$ of all functions on $G$, viewed as a module over $H$ acting by right translation through $\iota$: equivariant maps into it extend from stable subspaces. It is used in the construction of archimedean cut-off projectors and right-convolution operators on spaces of automorphic forms, for instance by [`AutomorphicForm.exists_linearMap_archCutProjector_comm_rightTranslate`](thm.html#AutomorphicForm.exists_linearMap_archCutProjector_comm_rightTranslate) and [`AutomorphicForm.exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq`](thm.html#AutomorphicForm.exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_exists_extend_forall_apply_mul_of_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem Representation.exists_extend_forall_apply_mul_of_injective
    {H : Type u} {G : Type v} [Group H] [Group G] {W : Type w} [AddCommGroup W] [Module ℂ W]
    (ι : H →* G) (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ k : H, ∀ v ∈ P, ρ k v ∈ P)
    (T : P →ₗ[ℂ] (G → ℂ))
    (hT : ∀ (k : H) (v : P) (x : G), T ⟨ρ k v, hP k v v.2⟩ x = T v (x * ι k)) :
    ∃ T' : W →ₗ[ℂ] (G → ℂ),
      (∀ (k : H) (v : W) (x : G), T' (ρ k v) x = T' v (x * ι k)) ∧ ∀ v : P, T' v = T v := by sorry
