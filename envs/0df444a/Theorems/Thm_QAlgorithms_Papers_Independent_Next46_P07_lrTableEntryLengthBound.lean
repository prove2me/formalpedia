-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P07_lrTableEntryLengthBound
-- name    : QAlgorithms.Papers.Independent.Next46.P07.lrTableEntryLengthBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:55:19.50892+00:00
-- url     : https://prove2.me/theorems/6c0d424d-21f8-4c59-ae3c-7e5ca3dbeb06
-- title:
--   Length support of every LR-contingency-table entry
-- statement:
--   Let $n>0$ and let $\mu_i=(\mu_i^+,\mu_i^-)$, $1\le i\le r$, be rational $GL(n,\mathbb C)$ labels of combined length at most $n$. Let $\Lambda=(\lambda_{ij})$ be a matrix of partitions whose weight $\prod_i\operatorname{LRC}^{\mu_i^+}_{\lambda_{i\bullet}}\operatorname{LRC}^{\mu_i^-}_{\lambda_{\bullet i}}$ is nonzero. Here each coefficient is an actual polynomial tensor multiplicity, equivalently the complex dimension of its equivariant Hom space. Then
--
--   $$\ell(\lambda_{ij})\le\min\{\ell(\mu_i^+),\ell(\mu_j^-)\}\qquad(1\le i,j\le r).$$
--
--   This support bound applies to all LR tables, without hollowness or a stable-range assumption. In particular, an empty row or column margin forces the corresponding entries to be empty.
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, PDF p. 7, lr-table-entry-length-bound

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Entry-length support bound (arXiv:2012.06928v1, PDF p.7, after Definition 2).
No hollow or stable-range condition is imposed. -/
theorem lrTableEntryLengthBound (n r : ℕ) (hn : 0 < n)
    (mu : Fin r → RationalLabel) (hmu : ∀ i, RationalLabelFits n (mu i))
    (table : Fin r → Fin r → YoungDiagram) (htable : IsLRTable mu table) :
    ∀ i j, (table i j).colLen 0 ≤ min ((mu i).1.colLen 0) ((mu j).2.colLen 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P07

end
