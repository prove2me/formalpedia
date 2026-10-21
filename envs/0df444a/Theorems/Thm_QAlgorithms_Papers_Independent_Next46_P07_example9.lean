-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P07_example9
-- name    : QAlgorithms.Papers.Independent.Next46.P07.example9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:58:55.553565+00:00
-- url     : https://prove2.me/theorems/b6f57bfb-ec47-40f8-ad7e-8d97e9f6e404
-- title:
--   A repeated-part hook tensor multiplicity equals one
-- statement:
--   Let $r\ge1$ and $s\ge r^2+r$ be integers, and let $n>r+s$. For a partition $\nu$, write $F_n^\nu$ for the irreducible polynomial representation of $GL(n,\mathbb C)$. Superscripts on parts below mean repetition: $((r+1)^r,r^s)$ has $r$ parts equal to $r+1$ and $s$ parts equal to $r$, and $(r+1,1^s)$ has one part $r+1$ followed by $s$ ones. Then
--
--   $$\dim_{\mathbb C}\operatorname{Hom}_{GL_n}\!\left(F_n^{((r+1)^r,r^s)},\left(F_n^{(r+1,1^s)}\right)^{\otimes r}\right)=1.$$
--
--   This is a specific occurrence with multiplicity one in a tensor power of a hook module. The statement retains the strict rank bound $n>r+s$ for all such ranks, rather than only the smallest rank used in the proof.
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, PDF p. 11, Example 9

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Example 9, (4.2) (arXiv:2012.06928v1, PDF pp.11-12). Replicate encodes
repeated parts, and the strict rank bound is the source's n>r+s. -/
theorem example9 (n r s : ℕ) (hr : 1 ≤ r) (hs : r ^ 2 + r ≤ s)
    (hstable : r + s < n) :
    homDimension
      (polynomialModel n (diagram (List.replicate r (r + 1) ++ List.replicate s r)))
      (tensorModel fun _ : Fin r =>
        polynomialModel n (diagram ((r + 1) :: List.replicate s 1))) = 1 := by sorry

end QAlgorithms.Papers.Independent.Next46.P07

end
