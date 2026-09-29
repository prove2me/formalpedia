-- Prove2me | Theorems.Thm_Submodule_finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image
-- name    : Submodule.finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/a54db74f-8364-569a-8f6d-a2d69e524200
-- title:
--   Base change preserves dimensions of complementary lattices in S²
-- statement:
--   Let $S$ be a commutative ring, $K$ a field and $S \to K$ an algebra structure. Let $L_0, L_1$ be $S$-submodules of $S^2$ (the module $\mathrm{Fin}\,2 \to S$) that are complementary, i.e. $L_0 \sqcap L_1 = \bot$ and $L_0 \sqcup L_1 = \top$, and let $M_0, M_1$ be complementary $K$-subspaces of $K^2$. Assume moreover that $M_0$ is the $K$-span of the image of $L_0$ under the coordinatewise map $v \mapsto \mathrm{algebraMap}\,S\,K \circ v$ from $S^2$ to $K^2$, and that $M_1$ is likewise the $K$-span of the image of $L_1$. The conclusion is the conjunction of two equalities of $K$-dimensions: $\dim_K (K \otimes_S L_0) = \dim_K M_0$ and $\dim_K (K \otimes_S L_1) = \dim_K M_1$, where the tensor products are taken over $S$ with $K$ acting through its left factor and $\mathrm{finrank}$ denotes the finite rank (zero for infinite-dimensional modules, though this case does not occur here).
--
--   A piece of linear algebra over a ring mapping to a field: base change along $S \to K$ of a direct sum decomposition of $S^2$ computes the dimensions of the complementary subspaces of $K^2$ spanned by the images. It is used in the study of idempotents and special subspaces, being cited by [`CerednikDrinfeld.FormalODModule.exists_idempotent_isSpecial_map_iff`](thm.html#CerednikDrinfeld.FormalODModule.exists_idempotent_isSpecial_map_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Submodule.finrank_baseChange_eq_finrank_of_isCompl_of_eq_span_image
    {S : Type} [CommRing S] {K : Type} [Field K] [Algebra S K]
    (L₀ L₁ : Submodule S (Fin 2 → S)) (hL : IsCompl L₀ L₁)
    (M₀ M₁ : Submodule K (Fin 2 → K)) (hM : IsCompl M₀ M₁)
    (h₀ : M₀ = Submodule.span K ((fun v : Fin 2 → S => ⇑(algebraMap S K) ∘ v) '' (L₀ : Set (Fin 2 → S))))
    (h₁ : M₁ = Submodule.span K ((fun v : Fin 2 → S => ⇑(algebraMap S K) ∘ v) '' (L₁ : Set (Fin 2 → S)))) :
    Module.finrank K (K ⊗[S] ↥L₀) = Module.finrank K ↥M₀ ∧ Module.finrank K (K ⊗[S] ↥L₁) = Module.finrank K ↥M₁ := by sorry
