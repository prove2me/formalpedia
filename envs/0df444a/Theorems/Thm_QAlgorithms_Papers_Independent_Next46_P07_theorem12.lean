-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P07_theorem12
-- name    : QAlgorithms.Papers.Independent.Next46.P07.theorem12
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:59:32.679522+00:00
-- url     : https://prove2.me/theorems/66584f81-5c7f-4d9e-9091-65bc1d57d0f0
-- title:
--   Orthogonal and symplectic invariants as symmetric weighted LR tables
-- statement:
--   Let $n>0$ and let $\mu=(\mu_1,\ldots,\mu_r)$ be partitions with $n\ge2\sum_i\ell(\mu_i)$. Let $E_n^{\mu_i}$ be the irreducible harmonic tensor representation of the full complex orthogonal group $O(n,\mathbb C)$, and let $V_{2n}^{\mu_i}$ be the irreducible highest-weight representation of $Sp(2n,\mathbb C)$. The range implies $\mu_i'(1)+\mu_i'(2)\le n$ and $\ell(\mu_i)\le n$, respectively. For a symmetric square matrix of partitions $\Lambda$, put $\llbracket\Lambda\rrbracket_\mu=\prod_i\operatorname{LRC}^{\mu_i}_{\lambda_{i\bullet}}$, with polynomial coefficients defined by equivariant Hom dimensions. A hollow symmetric LR table has empty diagonal and nonzero such weight. Then
--
--   $$\dim_{\mathbb C}\left(\bigotimes_i E_n^{\mu_i}\right)^{O_n}=\dim_{\mathbb C}\left(\bigotimes_i V_{2n}^{\mu_i}\right)^{Sp_{2n}}=\sum_{\Lambda\text{ hollow symmetric LR}}\llbracket\Lambda\rrbracket_\mu.$$
--
--   Each symmetric matrix is counted once and each row coefficient appears once. This extends the weighted invariant formula to the two other complex classical groups, without asserting equality of arbitrary same-label tensor multiplicities.
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, PDF p. 12, Theorem 12

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Theorem 12 (arXiv:2012.06928v1, PDF pp.13-14): both invariant dimensions
and their common row-weighted sum. The orthogonal group is the full complex O_n. -/
theorem theorem12 (n r : ℕ) (hn : 0 < n) (mu : Fin r → YoungDiagram)
    (hstable : 2 * (∑ i, (mu i).colLen 0) ≤ n) :
    invariantDimension (tensorModel fun i => orthogonalModel n (mu i)) =
      invariantDimension (tensorModel fun i => symplecticModel n (mu i)) ∧
    invariantDimension (tensorModel fun i => symplecticModel n (mu i)) =
      hollowSymmetricLRSum mu := by sorry

end QAlgorithms.Papers.Independent.Next46.P07

end
