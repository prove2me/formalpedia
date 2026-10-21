-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P07_example14
-- name    : QAlgorithms.Papers.Independent.Next46.P07.example14
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:01:04.613597+00:00
-- url     : https://prove2.me/theorems/e80f50f4-63c0-4a65-9c4d-8fc1cd6ac36b
-- title:
--   Adjoint tensor invariants count hollow symmetric tables of margin two
-- statement:
--   Let $r\ge0$ and $n\ge2$, with $n\ge2r$. Let $V=V_{2n}^{(2)}$ be the adjoint representation of $Sp(2n,\mathbb C)$ and $E=E_n^{(1,1)}$ the full orthogonal-group representation labeled by $(1,1)$. Set
--
--   $$c_r=\#\left\{T\in\mathbb Z_{\ge0}^{r\times r}:\ T=T^{\mathsf T},\ T_{ii}=0,\ \sum_jT_{ij}=2,\ \sum_iT_{ij}=2\right\}.$$
--
--   Then
--
--   $$\dim_{\mathbb C}(V^{\otimes r})^{Sp_{2n}}=c_r,\qquad\dim_{\mathbb C}(E^{\otimes r})^{O_n}=c_r.$$
--
--   The two labels differ, and the orthogonal action includes every component of $O(n,\mathbb C)$. At $r=0$ the unique empty table and both invariant dimensions are one. This is a shared counting description for these particular adjoint tensor families.
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, PDF p. 14, Example 14

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Example 14 (arXiv:2012.06928v1, PDF pp.14-15): Sp label (2), O label
(1,1), and hollow symmetric integer tables with all margins two. n≥2 makes
the O label valid even when the tensor is empty. -/
theorem example14 (n r : ℕ) (hn : 2 ≤ n) (hstable : 2 * r ≤ n) :
    let count := contingencyCount (fun _ : Fin r => 2) (fun _ : Fin r => 2)
      (fun T => (∀ i, T i i = 0) ∧ ∀ i j, T i j = T j i)
    invariantDimension (tensorModel fun _ : Fin r => symplecticModel n (rowPartition 2)) =
      count ∧
    invariantDimension (tensorModel fun _ : Fin r => orthogonalModel n (columnPartition 2)) =
      count := by sorry

end QAlgorithms.Papers.Independent.Next46.P07

end
