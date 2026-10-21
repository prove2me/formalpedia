-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P07_corollary4
-- name    : QAlgorithms.Papers.Independent.Next46.P07.corollary4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:55:58.284777+00:00
-- url     : https://prove2.me/theorems/860dc97a-39d0-4289-a7cc-bb89fb8eaa15
-- title:
--   One-row rational labels give ordinary hollow contingency tables
-- statement:
--   Let $n>0$, let $r\ge0$, and let $a_i,b_i$ be nonnegative integers. Assume $n\ge2r$. Write $\mu_i=((a_i),(b_i))$ for the rational $GL(n,\mathbb C)$ label obtained by padding between $a_i$ and $-b_i$; a zero degree means an empty partition. Then
--
--   $$\dim_{\mathbb C}\operatorname{Hom}_{GL_n}\!\left(\mathbb C,\bigotimes_{i=1}^rF_n^{\mu_i}\right)=\#\left\{T\in\mathbb Z_{\ge0}^{r\times r}:\ \sum_jT_{ij}=a_i,\ \sum_iT_{ij}=b_j,\ T_{ii}=0\right\}.$$
--
--   The left side is $\operatorname{LRC}^0_\mu$. No equality of total margins is assumed; unequal totals yield zero tables and zero multiplicity. This specializes the weighted formula to an unweighted hollow-table count.
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, PDF p. 9, Corollary 4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Corollary 4 (arXiv:2012.06928v1, PDF pp.9-10). Zero degrees denote empty
partitions and unequal total margins are permitted. -/
theorem corollary4 (n r : ℕ) (hn : 0 < n) (hstable : 2 * r ≤ n)
    (a b : Fin r → ℕ) :
    rationalLRC n (⊥, ⊥) (fun i => (rowPartition (a i), rowPartition (b i))) =
      contingencyCount a b (fun T => ∀ i, T i i = 0) := by sorry

end QAlgorithms.Papers.Independent.Next46.P07

end
