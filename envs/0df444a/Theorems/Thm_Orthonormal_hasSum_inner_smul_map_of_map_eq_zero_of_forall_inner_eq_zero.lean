-- Prove2me | Theorems.Thm_Orthonormal_hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero
-- name    : Orthonormal.hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/668983cf-077f-5530-8aad-b0a8eb974c78
-- title:
--   Orthonormal expansion passes through a vanishing continuous operator
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$ (an `RCLike` field), let $E$ be a complete normed $\mathbb{K}$-inner product space, let $F$ be a normed $\mathbb{K}$-vector space, and let $\iota$ be an arbitrary index type. Given a family $b \colon \iota \to E$ which is orthonormal for the inner product on $E$, a continuous $\mathbb{K}$-linear map $T \colon E \to F$, and the hypothesis that $T$ kills every vector orthogonal to the whole family, i.e. $Tv = 0$ whenever $\langle b_i, v\rangle = 0$ for all $i$, the conclusion is that for each $u \in E$ the family $i \mapsto \langle b_i, u \rangle \cdot T(b_i)$ is summable in $F$ with sum $T u$; in Lean terms, `HasSum (fun i => ⟪b i, u⟫_𝕜 • T (b i)) (T u)`, so the convergence is unconditional in the net-of-finite-partial-sums sense. No assumption is made that the family is total in $E$, nor that $\iota$ is countable, nor that $F$ is complete.
--
--   This is the standard fact that an orthonormal expansion may be applied term by term under a continuous linear map which annihilates the orthogonal complement of the family; the family need only be orthonormal, the vanishing hypothesis supplying what totality would otherwise give. It serves as the abstract projection-and-expansion step used in [`AutomorphicForm.hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule`](thm.html#AutomorphicForm.hasSum_setIntegral_mul_conj_mul_setIntegral_convOp_of_orthonormal_isotypicCuspSubmodule), where $E$ is a space of $L^2$ automorphic forms, $b$ an orthonormal system of cusp forms and $T$ a convolution operator followed by integration over a measurable set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Orthonormal_hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped InnerProductSpace

theorem Orthonormal.hasSum_inner_smul_map_of_map_eq_zero_of_forall_inner_eq_zero
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {ι : Type*} (b : ι → E) (hb : Orthonormal 𝕜 b) (T : E →L[𝕜] F)
    (hT : ∀ v : E, (∀ i, ⟪b i, v⟫_𝕜 = 0) → T v = 0) (u : E) :
    HasSum (fun i => ⟪b i, u⟫_𝕜 • T (b i)) (T u) := by sorry
