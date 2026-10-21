-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P26_weightedBranching
-- name    : QAlgorithms.Papers.Independent.Next46.P26.weightedBranching
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:04:52.285382+00:00
-- url     : https://prove2.me/theorems/026d3a5a-bf9f-4de0-9912-05f0279e8cc6
-- title:
--   Four weighted branching identities
-- statement:
--   Let $\lambda$ be a nonempty finite Young diagram in English coordinates, with $\ell$ rows and $m$ columns. Let $x_1,\ldots,x_\ell,y_1,\ldots,y_m$ be independent formal commutative variables over $\mathbb Q$. All the following equalities are in their rational function field. Write $C[\lambda]$ for the occupied corners, $\lambda_i$ for row lengths and $\lambda'_j$ for column lengths. For a corner $(r,s)$ define
--   $$
--   \Pi_{rs}=x_ry_s\prod_{i=1}^{r-1}\left(1+\frac{x_i}{\sum_{k=i+1}^r x_k+\sum_{l=s+1}^{\lambda_i}y_l}\right)\prod_{j=1}^{s-1}\left(1+\frac{y_j}{\sum_{k=r+1}^{\lambda'_j}x_k+\sum_{l=j+1}^s y_l}\right).
--   $$
--   Put $W=\sum_{(p,q)\in[\lambda]}x_py_q$, $A_{rs}=\sum_{k=r+1}^{\ell}x_k+\sum_{l=1}^s y_l$, and $B_{rs}=\sum_{k=1}^r x_k+\sum_{l=s+1}^{m}y_l$. Then
--   $$
--   \sum_{(r,s)\in C[\lambda]}\Pi_{rs}=W,\quad
--   \sum_{(r,s)\in C[\lambda]}\frac{\Pi_{rs}}{A_{rs}}=\sum_{i=1}^{\ell}x_i,\quad
--   \sum_{(r,s)\in C[\lambda]}\frac{\Pi_{rs}}{B_{rs}}=\sum_{j=1}^{m}y_j,\quad
--   \sum_{(r,s)\in C[\lambda]}\frac{\Pi_{rs}}{A_{rs}B_{rs}}=1.
--   $$
--   These are the weighted branching rule and its three companion identities. Empty products are one and empty sums zero.
-- source:
--   The weighted hook length formula, arXiv:1006.0043v1, PDF p. 6, Theorem 2(a)–(d)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Theorem 2(a–d), p.6 (WHL also p.2): all four identities in the
fraction field of independent formal row/column indeterminates. -/
theorem weightedBranching (lam : YoungDiagram) (hne : lam.cells.Nonempty) :
    ((∑ z ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) z.1 z.2) =
      totalWeight lam (ratX lam) (ratY lam)) ∧
    ((∑ z ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) z.1 z.2 /
      outsideA lam (ratX lam) (ratY lam) z.1 z.2) =
      ∑ i ∈ Finset.range (lam.colLen 0), ratX lam i) ∧
    ((∑ z ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) z.1 z.2 /
      outsideB lam (ratX lam) (ratY lam) z.1 z.2) =
      ∑ j ∈ Finset.range (lam.rowLen 0), ratY lam j) ∧
    ((∑ z ∈ corners lam, cornerWeight lam (ratX lam) (ratY lam) z.1 z.2 /
      (outsideA lam (ratX lam) (ratY lam) z.1 z.2 *
        outsideB lam (ratX lam) (ratY lam) z.1 z.2)) = 1) := by sorry

end QAlgorithms.Papers.Independent.Next46.P26

end
