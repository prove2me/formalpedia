-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P07_example5
-- name    : QAlgorithms.Papers.Independent.Next46.P07.example5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T12:56:33.393733+00:00
-- url     : https://prove2.me/theorems/02768c45-f7ab-4c0b-ba27-581772a01913
-- title:
--   Adjoint-component tensor invariants and derangements
-- statement:
--   Let $r\ge0$ and $n\ge2$, with $n\ge2r$. Let $A_n=F_n^{((1),(1))}$ be the nontrivial adjoint component of the rational $GL(n,\mathbb C)$ representation on $\mathfrak{gl}_n$. Let $!r$ count permutations of $r$ letters with no fixed point. For the diagonal action,
--
--   $$\dim_{\mathbb C}(A_n^{\otimes r})^{GL_n}=!r.$$
--
--   The zeroth tensor power is $\mathbb C$, and $!0=1$. The separate condition $n\ge2$ keeps the adjoint label admissible even for the empty tensor. This identifies adjoint-component tensor invariants with a familiar permutation count.
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, PDF p. 10, Example 5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Example 5 (arXiv:2012.06928v1, PDF p.10). The nontrivial adjoint component
has label ((1),(1)); n≥2 also makes that label valid for the empty tensor. -/
theorem example5 (n r : ℕ) (hn : 2 ≤ n) (hstable : 2 * r ≤ n) :
    invariantDimension (tensorModel fun _ : Fin r =>
      rationalModel n (rowPartition 1, rowPartition 1)) = derangements r := by sorry

end QAlgorithms.Papers.Independent.Next46.P07

end
