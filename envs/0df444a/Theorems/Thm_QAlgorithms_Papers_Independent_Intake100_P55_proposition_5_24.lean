-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P55_proposition_5_24
-- name    : QAlgorithms.Papers.Independent.Intake100.P55.proposition_5_24
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:58:50.12386+00:00
-- url     : https://prove2.me/theorems/d8d41162-b16d-4b56-8579-74f64d9d88d1
-- title:
--   Proposition 5.24
-- statement:
--   Let $R$ be a commutative unital ring with units $\lambda,\delta$ and $z\in R$ satisfying $\lambda^{-1}-\lambda=z(\delta-1)$. For the affine algebra specify arbitrary scalars $q_s$ for every positive integer $s$, with no admissibility or cyclotomic condition. Write $W_n$ and $\widehat W_n$ for the ordinary and affine BMW presentations of Definitions 3.1 and 3.6. Lower levels denote their canonical generator images; products of subspaces denote their $R$-linear spans.
--
--   Let $k\ge1$ and define $f_1=e_1$ and, recursively, $f_k=(g_1\cdots g_{2k-2})f_{k-1}e_{2k-1}(g_{2k-2}\cdots g_1)$ in $W_{2k}$. For $0\le j<k$, write $C_j=e_{k-j}e_{k-j+2}\cdots e_{k+j}$. Then
--   $$f_k=C_0C_1\cdots C_{k-1}C_{k-2}\cdots C_0.$$
--   The last reverse sequence is empty at $k=1$. Thus $f_1=e_1$, and the expression is a diamond word involving only contractions.
-- source:
--   Affine Birman-Wenzl-Murakami Algebras and Tangles in the Solid Torus, arXiv:math/0411155v2, PDF p. 40, Proposition 5.24

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P55

noncomputable section

open scoped Classical

namespace QAlgorithms.Papers.Independent.Intake100.P55

section Statements

variable {R : Type*} [CommRing R] (P : Ground R) (q : ℕ → R)

/-- Proposition 5.24, PDF pp.40--41. The recursive braid word equals the
diamond e-word; the repeated middle column is omitted. -/
theorem proposition_5_24 (k : ℕ) (hk : 1 ≤ k) :
    fElement P q (2*k) 0 k = diamondWord (ghContraction P q false (2*k)) k := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intake100.P55

end
