-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P03_reindexed_univ_qs_eval
-- name    : QAlgorithms.Papers.Independent.Next46.P03.reindexed_univ_qs_eval
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:35:11.937407+00:00
-- url     : https://prove2.me/theorems/bfeba5dc-8c06-4999-9d04-ac8153639ae2
-- title:
--   Evaluation commutes with conversion and lowering coefficient indices
-- statement:
--   Let $q_1,\ldots,q_m$ be an arbitrary ordered finite list of multivariate polynomials over $\mathbb R$ with variables indexed by $\mathbb N$. Let $x\in\mathbb R$ and let $L$ be any finite list of real numbers. Write $E_L(q)$ for polynomial evaluation that assigns variable $j$ the entry at position $j$ of $L$, or zero if that position is absent. For each $q_i$, first convert it to a univariate polynomial in variable zero; then lower every variable index in each coefficient by one, obtaining $r_i$. Write $E_L^*(r_i)$ for the univariate real polynomial obtained by evaluating those coefficients on $L$. Then the following is equality of lists, preserving order and multiplicity:
--
--   $$
--   [\,E_{x::L}(q_i)\,]_{i=1}^{m}
--   =
--   [\,(E_L^*(r_i))(x)\,]_{i=1}^{m}.
--   $$
--
--   This is the evaluation identity needed when removing the innermost variable and reindexing the remaining free variables. Empty polynomial lists and empty valuation lists are permitted. The conversion itself ensures that the coefficients have no variable zero before indices are lowered.
-- source:
--   A First Complete Algorithm for Real Quantifier Elimination in Isabelle/HOL, arXiv:2209.10978v2, PDF p. 11, §3.3: lemma reindexed_univ_qs_eval

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P03

namespace QAlgorithms.Papers.Independent.Next46.P03

noncomputable section

/-- Kosaian–Tan–Platzer, arXiv:2209.10978v2, §3.3, PDF pp. 11–12,
`reindexed_univ_qs_eval`. The two constructed lists from the source's
premises are substituted directly into its conclusion. Both valuations
use zero beyond their finite lists; empty lists are allowed. -/
theorem reindexed_univ_qs_eval (qs : List (MvPolynomial ℕ ℝ))
    (x : ℝ) (xs : List ℝ) :
    qs.map (fun p => evalMpoly (x :: xs) p) =
      (((univariateIn qs 0).map (fun p => p.map lowerPolyZeroOne)).map
        (fun q => evalMpolyPoly xs q)).map (fun p => p.eval x) := by sorry

end

end QAlgorithms.Papers.Independent.Next46.P03
