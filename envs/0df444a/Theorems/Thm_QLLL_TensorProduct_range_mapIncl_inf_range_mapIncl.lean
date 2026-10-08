-- Prove2me | Theorems.Thm_QLLL_TensorProduct_range_mapIncl_inf_range_mapIncl
-- name    : QLLL.TensorProduct.range_mapIncl_inf_range_mapIncl
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:00.99798+00:00
-- url     : https://prove2.me/theorems/bfa40463-93a7-4885-8b5f-0899cb3407de
-- title:
--   Tensor products of subspaces intersect factorwise: $(A \otimes B) \cap (A' \otimes B') = (A \cap A') \otimes (B \cap B')$
-- statement:
--   Let $\mathbb{K}$ be a field and let $V, W$ be vector spaces over $\mathbb{K}$. For subspaces $A \subseteq V$ and $B \subseteq W$ write $A \otimes B$ for the subspace of $V \otimes_{\mathbb{K}} W$ spanned by the pure tensors $a \otimes b$ with $a \in A$, $b \in B$. In Lean this subspace is Mathlib's `LinearMap.range (TensorProduct.mapIncl A B)`, the image of the map $A \otimes B \to V \otimes W$ induced by the two inclusions. For subspaces $A, A' \subseteq V$ and $B, B' \subseteq W$,
--   $$(A \otimes B) \cap (A' \otimes B') \ =\ (A \cap A') \otimes (B \cap B').$$
--
--   This is the linear-algebra fact behind the tensor-product computation in Lemma 11 of Ambainis, Kempe and Sattath, where constraints acting on disjoint qubits are shown to be mutually R-independent. It is the intersection counterpart of the standard identity for sums of tensor products of subspaces, and is a candidate for Mathlib.
--
--   **Formalization Note** No finite-dimensionality is assumed. On the platform the name carries a `QLLL.` prefix so that it cannot clash with Mathlib if an equivalent lemma is added there later.
-- source:
--   Not in the paper; general linear algebra used in the tensor-product computation of Lemma 11. formalization companion to Ambainis, Kempe and Sattath, A Quantum Lovász Local Lemma, arXiv:0911.1696; see the blueprint https://sattath.github.io/Quantum-Lovasz-Local-Lemma/blueprint/

import Mathlib

open TensorProduct LinearMap Function
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
open _root_.TensorProduct
variable (A A' : Submodule K V) (B B' : Submodule K W)

theorem QLLL.TensorProduct.range_mapIncl_inf_range_mapIncl :
    LinearMap.range (TensorProduct.mapIncl A B)
        ⊓ LinearMap.range (TensorProduct.mapIncl A' B')
      = LinearMap.range (TensorProduct.mapIncl (A ⊓ A') (B ⊓ B')) := by sorry
