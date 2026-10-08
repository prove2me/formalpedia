-- Prove2me | Theorems.Thm_QLLL_LinearMap_exists_comp_add_comp
-- name    : QLLL.LinearMap.exists_comp_add_comp
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:45:32.700336+00:00
-- url     : https://prove2.me/theorems/4d157781-01bb-4225-bc27-799e19f3f158
-- title:
--   A linear map vanishing on $\ker f \cap \ker g$ factors as $u \circ f + v \circ g$
-- statement:
--   Let $\mathbb{K}$ be a field and let $V, M, N, H$ be vector spaces over $\mathbb{K}$. Let $f : V \to M$, $g : V \to N$ and $h : V \to H$ be linear maps with
--   $$\ker f \cap \ker g \ \subseteq\ \ker h.$$
--   Then there are linear maps $u : M \to H$ and $v : N \to H$ such that
--   $$h \ =\ u \circ f + v \circ g.$$
--
--   This factorization lemma is the key step in identifying the intersection of two tensor products of subspaces, `QLLL.TensorProduct.range_mapIncl_eq_inf` and `QLLL.TensorProduct.range_mapIncl_inf_range_mapIncl`.
--
--   **Formalization Note** No finite-dimensionality is assumed; the field hypothesis is essential. On the platform the name carries a `QLLL.` prefix so that it cannot clash with Mathlib if an equivalent lemma is added there later.
-- source:
--   Not in the paper; general linear algebra supporting the tensor-product computation of Lemma 11. Formalization companion to Ambainis, Kempe and Sattath, A Quantum Lovász Local Lemma, arXiv:0911.1696; see the blueprint https://sattath.github.io/Quantum-Lovasz-Local-Lemma/blueprint/

import Mathlib

open TensorProduct LinearMap Function
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
open _root_.LinearMap
variable {M N H : Type*}
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup H] [Module K H]

theorem QLLL.LinearMap.exists_comp_add_comp (f : V →ₗ[K] M) (g : V →ₗ[K] N) (h : V →ₗ[K] H)
    (hker : ker f ⊓ ker g ≤ ker h) :
    ∃ (u : M →ₗ[K] H) (v : N →ₗ[K] H), h = u ∘ₗ f + v ∘ₗ g := by sorry
