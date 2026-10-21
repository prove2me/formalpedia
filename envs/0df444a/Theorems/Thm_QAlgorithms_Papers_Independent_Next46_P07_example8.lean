-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P07_example8
-- name    : QAlgorithms.Papers.Independent.Next46.P07.example8
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:58:13.766987+00:00
-- url     : https://prove2.me/theorems/44b35701-2aee-4b7c-bb0e-7752aa4c303f
-- title:
--   Hom dimension between exterior and symmetric tensors for a Young diagram
-- statement:
--   Let $\lambda$ be a partition with $r=\ell(\lambda)$ rows, $s=\lambda_1$ columns, and size $|\lambda|$. Write $\lambda'_j$ for its column heights. Let $n>0$ satisfy $n\ge r+|\lambda|$. For the natural $GL(n,\mathbb C)$ actions,
--
--   $$\dim_{\mathbb C}\operatorname{Hom}_{GL_n}\!\left(\bigotimes_{j=1}^s\bigwedge^{\lambda'_j}\mathbb C^n,\bigotimes_{i=1}^r S^{\lambda_i}\mathbb C^n\right)=1.$$
--
--   Both tensors may be reducible, and the bracket in the source means this full Hom dimension. For the empty partition both tensors are the trivial complex line. This relates the row and column descriptions of a Young diagram through a multiplicity-one Hom space.
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, PDF p. 11, Example 8

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Example 8, (4.1) (arXiv:2012.06928v1, PDF p.11): the exterior tensor is
the Hom domain and may be reducible; column heights and row lengths are distinct. -/
theorem example8 (n : ℕ) (hn : 0 < n) (lambda : YoungDiagram)
    (hstable : lambda.colLen 0 + lambda.card ≤ n) :
    homDimension
      (tensorModel fun j : Fin (lambda.rowLen 0) =>
        polynomialModel n (columnPartition (lambda.colLen j.val)))
      (tensorModel fun i : Fin (lambda.colLen 0) =>
        polynomialModel n (rowPartition (lambda.rowLen i.val))) = 1 := by sorry

end QAlgorithms.Papers.Independent.Next46.P07

end
