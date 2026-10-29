-- Prove2me | Theorems.Thm_PochetWolsey_Decomposition_tu_column_partition
-- name    : PochetWolsey.Decomposition.tu_column_partition
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:47.911296+00:00
-- url     : https://prove2.me/theorems/21ac6500-3e18-4e36-b0ab-95085feb0778
-- title:
--   Proposition 6.6 — column-partition test for total unimodularity
-- statement:
--   Let $A\in\{0,1,-1\}^{m\times n}$. Suppose that every subset $J$ of its columns can be partitioned into disjoint sets $J_1,J_2$ such that, for each row $i$,
--   $$
--   \left|\sum_{j\in J_1}a_{ij}-\sum_{j\in J_2}a_{ij}\right|\le1.
--   $$
--   Then $A$ is totally unimodular: every square submatrix has determinant in $\{0,1,-1\}$. This is a sufficient recognition criterion used in integral formulation arguments.
--
--   **Formalization Note** Matrices have real entries with the displayed entry restriction. Finite indices start at zero; an empty row or column family is allowed and satisfies the usual determinant convention.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 204 (PDF 218), Proposition 6.6

import Mathlib

namespace PochetWolsey.Decomposition

theorem tu_column_partition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hentries : ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1)
    (hpartition : ∀ J : Finset (Fin n), ∃ J₁ J₂ : Finset (Fin n),
      Disjoint J₁ J₂ ∧ J₁ ∪ J₂ = J ∧
      ∀ i, |(∑ j ∈ J₁, A i j) - ∑ j ∈ J₂, A i j| ≤ 1) :
    A.IsTotallyUnimodular := by sorry

end PochetWolsey.Decomposition
