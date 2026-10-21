-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P07_corollary6
-- name    : QAlgorithms.Papers.Independent.Next46.P07.corollary6
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:56:56.773754+00:00
-- url     : https://prove2.me/theorems/c8f79383-6e66-4d9f-b323-e1d10dccda47
-- title:
--   Hom dimensions between symmetric-power tensors count rectangular tables
-- statement:
--   Let $n>0$, let $r,s\ge0$, and assume $n\ge r+s$. For nonnegative integers $a_i$ and $b_j$, let $F_n^{(a_i)}$ and $F_n^{(b_j)}$ denote the corresponding one-row polynomial $GL(n,\mathbb C)$ modules, including the trivial module in degree zero. Then
--
--   $$\dim_{\mathbb C}\operatorname{Hom}_{GL_n}\!\left(\bigotimes_{i=1}^rF_n^{(a_i)},\bigotimes_{j=1}^sF_n^{(b_j)}\right)=\#\left\{T\in\mathbb Z_{\ge0}^{r\times s}:\ \sum_jT_{ij}=a_i,\ \sum_iT_{ij}=b_j\right\}.$$
--
--   There is no hollow constraint, and no assumption that the total margins agree. This expresses an equivariant Hom dimension as an ordinary rectangular-table count, preserving the displayed domain and codomain.
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, PDF p. 10, Corollary 6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Corollary 6 (arXiv:2012.06928v1, PDF p.10): rectangular tables, no hollow
condition, and the displayed a-tensor to b-tensor Hom orientation. -/
theorem corollary6 (n r s : ℕ) (hn : 0 < n) (hstable : r + s ≤ n)
    (a : Fin r → ℕ) (b : Fin s → ℕ) :
    homDimension (tensorModel fun i => polynomialModel n (rowPartition (a i)))
      (tensorModel fun j => polynomialModel n (rowPartition (b j))) =
      contingencyCount a b (fun _ => True) := by sorry

end QAlgorithms.Papers.Independent.Next46.P07

end
