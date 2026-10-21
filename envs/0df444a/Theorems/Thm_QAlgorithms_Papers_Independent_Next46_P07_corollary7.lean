-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P07_corollary7
-- name    : QAlgorithms.Papers.Independent.Next46.P07.corollary7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:57:49.487016+00:00
-- url     : https://prove2.me/theorems/6878d8e8-ba25-469a-902a-365b9dccdfcd
-- title:
--   Dimension of the commuting endomorphism algebra of tensor space
-- statement:
--   Let $n>0$, let $r\ge0$, and assume $n\ge2r$. Equip $(\mathbb C^n)^{\otimes r}$ with the diagonal defining action of $GL(n,\mathbb C)$. Then
--
--   $$\dim_{\mathbb C}\operatorname{End}_{GL_n}\!\left((\mathbb C^n)^{\otimes r}\right)=r!.$$
--
--   The endomorphisms commute with every group element. For $r=0$ the space is $\mathbb C$ and both sides are one. The formula counts permutation matrices through the preceding rectangular-table specialization; it concerns the commuting endomorphism algebra rather than the tensor invariant space.
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, PDF p. 11, Corollary 7

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Corollary 7 (arXiv:2012.06928v1, PDF p.11): commuting endomorphisms,
with the source's sufficient range n≥2r and 0!=1. -/
theorem corollary7 (n r : ℕ) (hn : 0 < n) (hstable : 2 * r ≤ n) :
    let V := tensorModel fun _ : Fin r => polynomialModel n (rowPartition 1)
    homDimension V V = Nat.factorial r := by sorry

end QAlgorithms.Papers.Independent.Next46.P07

end
