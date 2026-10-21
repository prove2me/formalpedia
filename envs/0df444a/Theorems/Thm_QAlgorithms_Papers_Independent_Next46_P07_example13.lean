-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P07_example13
-- name    : QAlgorithms.Papers.Independent.Next46.P07.example13
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:00:15.030411+00:00
-- url     : https://prove2.me/theorems/837179b1-04bc-4fab-a7b9-01a8a4e29dce
-- title:
--   Defining tensor invariants and fixed-point-free involutions
-- statement:
--   Let $n>0$ and $r\ge0$ satisfy $n\ge2r$. Let $V_{2n}^{(1)}=\mathbb C^{2n}$ be the defining representation of $Sp(2n,\mathbb C)$, and $E_n^{(1)}=\mathbb C^n$ the defining representation of the full group $O(n,\mathbb C)$. Then
--
--   $$\dim_{\mathbb C}\left((V_{2n}^{(1)})^{\otimes r}\right)^{Sp_{2n}}=\dim_{\mathbb C}\left((E_n^{(1)})^{\otimes r}\right)^{O_n}=\begin{cases}\displaystyle\prod_{k=0}^{r/2-1}(2k+1),&r\text{ even},\\0,&r\text{ odd}.\end{cases}$$
--
--   The even product is $(r-1)!!$ for positive even $r$ and is the empty product one at $r=0$. These dimensions count fixed-point-free involutions of $r$ letters.
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, PDF p. 14, Example 13

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Example 13 (arXiv:2012.06928v1, PDF p.14): both defining modules, with
an even product that also handles the unique empty tensor at r=0. -/
theorem example13 (n r : ℕ) (hn : 0 < n) (hstable : 2 * r ≤ n) :
    invariantDimension (tensorModel fun _ : Fin r => symplecticModel n (rowPartition 1)) =
      invariantDimension (tensorModel fun _ : Fin r => orthogonalModel n (rowPartition 1)) ∧
    invariantDimension (tensorModel fun _ : Fin r => orthogonalModel n (rowPartition 1)) =
      pairingCount r := by sorry

end QAlgorithms.Papers.Independent.Next46.P07

end
