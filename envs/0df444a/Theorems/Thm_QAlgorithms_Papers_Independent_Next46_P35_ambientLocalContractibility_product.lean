-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P35_ambientLocalContractibility_product
-- name    : QAlgorithms.Papers.Independent.Next46.P35.ambientLocalContractibility_product
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T14:37:51.956802+00:00
-- url     : https://prove2.me/theorems/a5d0996c-536a-42cd-be5a-7fd659d708aa
-- title:
--   Ambient local contractibility and products
-- statement:
--   Let $X$ and $Y$ be topological spaces. Local contractibility at a point means that some neighborhood contracts to that point in the ambient space.
--
--   1. For $x_0\in X$ and $y_0\in Y$,
--
--   $$
--   X\times Y\text{ locally contractible at }(x_0,y_0)
--   \quad\Longrightarrow\quad Y\text{ locally contractible at }y_0.
--   $$
--
--   2. If $X$ is contractible and $Y$ is locally contractible at $y_0$, then
--
--   $$
--   \forall x_0\in X,\quad X\times Y\text{ is locally contractible at }(x_0,y_0).
--   $$
--
--   No global nonemptiness condition is imposed on arbitrary spaces. The points supply the required nonemptiness in the first clause, while contractibility supplies it in the second. These assertions isolate the product-space step used throughout the paper.
-- source:
--   Pro-Lie groups which are infinite-dimensional Lie groups, arXiv:math/0609684v1, PDF p. 39, Lemma 10.3

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P35

namespace QAlgorithms.Papers.Independent.Next46.P35

open Set Filter Topology

open scoped Manifold ContDiff

universe u v w z

/-- Lemma 10.3, PDF pp. 39–40: both product assertions, with the ambient
contraction convention of Definition 10.1. No global nonemptiness assumption is added. -/
theorem ambientLocalContractibility_product
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] :
    (∀ (x : X) (y : Y), AmbientLocallyContractibleAt (x, y) →
      AmbientLocallyContractibleAt y) ∧
    (ContractibleSpace X → ∀ y : Y, AmbientLocallyContractibleAt y →
      ∀ x : X, AmbientLocallyContractibleAt (x, y)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P35
