-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_proposition_3_10
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.proposition_3_10
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:52:31.152311+00:00
-- url     : https://prove2.me/theorems/1836d074-bc07-4770-b994-dfe557366013
-- title:
--   Proposition 3.10
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   In $\widehat W_n$ define $x_r=(g_{r-1}\cdots g_1)x_1(g_1\cdots g_{r-1})$ for $1\le r\le n$, with empty products at $r=1$. For every such $r$ and every $1\le j<n$ with $j\notin\{r,r-1\}$,
--   $$g_jx_r=x_rg_j,\qquad e_jx_r=x_re_j.$$
--   Furthermore, $x_jx_r=x_rx_j$ for all $1\le j,r\le n$. These commutation relations identify the commuting winding elements.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 19, Proposition 3.10

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Proposition 3.10(1)--(3), PDF p.19. All x indices lie in 1..n and
all g/e indices lie in 1..n-1. -/
theorem proposition_3_10 (n : ℕ) :
    (∀ r j, 1 ≤ r → r ≤ n → BMWIndex n j → j ≠ r → j+1 ≠ r →
      ghCrossing P q true n j false * bmwWinding P q n false r =
        bmwWinding P q n false r * ghCrossing P q true n j false) ∧
    (∀ r j, 1 ≤ r → r ≤ n → BMWIndex n j → j ≠ r → j+1 ≠ r →
      ghContraction P q true n j * bmwWinding P q n false r =
        bmwWinding P q n false r * ghContraction P q true n j) ∧
    (∀ r j, 1 ≤ r → r ≤ n → 1 ≤ j → j ≤ n →
      bmwWinding P q n false j * bmwWinding P q n false r =
        bmwWinding P q n false r * bmwWinding P q n false j) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
