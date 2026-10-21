-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P03_same_evaluations_same_mpoly
-- name    : QAlgorithms.Papers.Independent.Next46.P03.same_evaluations_same_mpoly
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T12:35:43.444062+00:00
-- url     : https://prove2.me/theorems/a90a0d95-994f-4001-99fc-d28af4e29906
-- title:
--   Finite-list evaluation determines a real multivariate polynomial
-- statement:
--   Let $p,q\in\mathbb R[X_0,X_1,\ldots]$ be multivariate polynomials with finite support. For a finite real list $L$, let $E_L$ assign variable $j$ the entry at position $j$ of $L$, using zero when $j$ is beyond the list. If the two evaluations agree for every finite list of every length, then
--
--   $$
--   \bigl(\forall L\in\operatorname{List}(\mathbb R),\ E_L(p)=E_L(q)\bigr)
--   \quad\Longrightarrow\quad p=q.
--   $$
--
--   This is polynomial extensionality for the finite-list evaluation convention used by the quantifier-elimination development. The coefficient field is specifically $\mathbb R$.
-- source:
--   A First Complete Algorithm for Real Quantifier Elimination in Isabelle/HOL, arXiv:2209.10978v2, PDF p. 12, §3.3: lemma same_evaluations_same_mpoly

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P03

namespace QAlgorithms.Papers.Independent.Next46.P03

noncomputable section

/-- Kosaian–Tan–Platzer, arXiv:2209.10978v2, §3.3, PDF p. 12,
`same_evaluations_same_mpoly`. Equality of evaluation is required for every
finite real list of every length, rather than a fixed-length valuation. -/
theorem same_evaluations_same_mpoly (p q : MvPolynomial ℕ ℝ)
    (h : ∀ xs : List ℝ, evalMpoly xs p = evalMpoly xs q) :
    p = q := by sorry

end

end QAlgorithms.Papers.Independent.Next46.P03
