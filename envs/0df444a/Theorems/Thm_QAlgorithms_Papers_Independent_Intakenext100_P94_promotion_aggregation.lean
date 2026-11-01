-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P94_promotion_aggregation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P94.promotion_aggregation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:46:20.285436+00:00
-- url     : https://prove2.me/theorems/8e31f046-74bf-4370-9c90-bb7a751abdac
-- title:
--   Promotion and covariance of sums and outer products
-- statement:
--   Let $\chi:[m]\hookrightarrow[n]$ be the injective child-to-parent correspondence and let $F$ be an order-$k$ child tensor. Define promotion by embedding each tensor index along $\chi$ and assigning zero off the image. For parent permutation $\sigma$ and child permutation $\pi$, relabel the correspondence as $\chi'=\sigma\circ\chi\circ\pi^{-1}$. Then
--
--   $$
--   \operatorname{promote}_{\chi'}(\pi F)=\sigma\bigl(\operatorname{promote}_{\chi}F\bigr).
--   $$
--
--   Finite sums of promoted activations transform covariantly, and the outer product of tensors of orders $k,l$ transforms covariantly as a tensor of order $k+l$:
--
--   $$
--   \sum_c\sigma F_c=\sigma\!\left(\sum_cF_c\right),\qquad (\sigma F)\otimes(\sigma G)=\sigma(F\otimes G).
--   $$
--
--   These operations provide the source’s sum and product aggregation rules on the parent domain. The correspondence must move with the relabelling. The zero extension fixes how contributions from overlapping child domains are combined.
-- source:
--   The general theory of permutation equivarant neural networks and higher order graph variational encoders, arXiv:2004.03990v1, PDF p. 6, §5, unnumbered: promotion and covariant sums/products

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P94

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Promotion and covariant sums/products, source PDF pp.5–6, Eq.(6).
Parent and child relabellings move chi to s∘chi∘p⁻¹. Empty domains/families
use the same finite-sum zero-extension convention. -/
theorem promotion_aggregation :
    (∀ {m n k : ℕ} (chi : Fin m ↪ Fin n) (F : Tensor m k) u,
      promote chi F (fun a => chi (u a)) = F u) ∧
    (∀ {m n k : ℕ} (chi : Fin m ↪ Fin n) (s : Perm n) (p : Perm m) (F : Tensor m k),
      promote (relabelEmbedding chi s p) (permutationTensorAction p F) =
        permutationTensorAction s (promote chi F)) ∧
    (∀ {n k : ℕ} {C : Type*} [Fintype C] (s : Perm n) (F : C → Tensor n k),
      (∑ a, permutationTensorAction s (F a)) = permutationTensorAction s (∑ a, F a)) ∧
    (∀ {n k l : ℕ} (s : Perm n) (F : Tensor n k) (G : Tensor n l) t,
      tensorOuterProduct (permutationTensorAction s F) (permutationTensorAction s G) t =
        tensorOuterProduct F G (fun a => s.symm (t a))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P94

end
