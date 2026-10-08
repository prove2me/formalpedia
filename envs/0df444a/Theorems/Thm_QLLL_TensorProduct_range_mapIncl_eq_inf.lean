-- Prove2me | Theorems.Thm_QLLL_TensorProduct_range_mapIncl_eq_inf
-- name    : QLLL.TensorProduct.range_mapIncl_eq_inf
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:45:39.269497+00:00
-- url     : https://prove2.me/theorems/0bdfbd8f-27a9-4111-b2f9-62d7003841cc
-- title:
--   $A \otimes B = (A \otimes W) \cap (V \otimes B)$ for subspaces over a field
-- statement:
--   Let $\mathbb{K}$ be a field and let $V, W$ be vector spaces over $\mathbb{K}$. For subspaces $A \subseteq V$ and $B \subseteq W$ write $A \otimes B$ for the subspace of $V \otimes_{\mathbb{K}} W$ spanned by the pure tensors $a \otimes b$ with $a \in A$, $b \in B$. In Lean this subspace is Mathlib's `LinearMap.range (TensorProduct.mapIncl A B)`, the image of the map $A \otimes B \to V \otimes W$ induced by the two inclusions. For every subspace $A \subseteq V$ and $B \subseteq W$,
--   $$A \otimes B \ =\ (A \otimes W) \cap (V \otimes B).$$
--
--   This reduces intersections of tensor products of subspaces to the one-sided subspaces $A \otimes W$ and $V \otimes B$, and is the main step towards the factorwise intersection formula `QLLL.TensorProduct.range_mapIncl_inf_range_mapIncl`. It is also used to identify extended constraints in the tensor-product form of the $k$-QSAT corollary.
--
--   **Formalization Note** No finite-dimensionality is assumed. On the platform the name carries a `QLLL.` prefix so that it cannot clash with Mathlib if an equivalent lemma is added there later.
-- source:
--   Not in the paper; general linear algebra used in the tensor-product computation of Lemma 11. formalization companion to Ambainis, Kempe and Sattath, A Quantum Lovász Local Lemma, arXiv:0911.1696; see the blueprint https://sattath.github.io/Quantum-Lovasz-Local-Lemma/blueprint/

import Mathlib

open TensorProduct LinearMap Function
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
open _root_.TensorProduct

theorem QLLL.TensorProduct.range_mapIncl_eq_inf (A : Submodule K V) (B : Submodule K W) :
    LinearMap.range (TensorProduct.mapIncl A B)
      = LinearMap.range (TensorProduct.mapIncl A (⊤ : Submodule K W))
        ⊓ LinearMap.range (TensorProduct.mapIncl (⊤ : Submodule K V) B) := by sorry
