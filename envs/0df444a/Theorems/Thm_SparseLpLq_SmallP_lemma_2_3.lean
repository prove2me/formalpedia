-- Prove2me | Theorems.Thm_SparseLpLq_SmallP_lemma_2_3
-- name    : SparseLpLq.SmallP.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:45:59.03662+00:00
-- url     : https://prove2.me/theorems/1d3058b5-9c75-40b5-ad0c-ce67a68554e2
-- title:
--   Lemma 2.3, p. 8 — two sorted vectors with equal power sums of orders 1, …, n are equal
-- statement:
--   Let $a=(a_1,\dots,a_n)^\top$ and $b=(b_1,\dots,b_n)^\top$ be vectors in $\mathbb R^n$ with nondecreasing entries, $a_1\le a_2\le\dots\le a_n$ and $b_1\le b_2\le\dots\le b_n$, and suppose their power sums agree up to order $n$:
--
--   $$\sum_{j=1}^n a_j^k=\sum_{j=1}^n b_j^k,\qquad k=1,\dots,n .$$
--
--   Then $a=b$.
--
--   The entries may be negative or zero, and the powers are ordinary integer powers. In the paper this lemma is applied to the logarithms $\ln|a_{i_j}|$ of the nonzero entries of two vectors, where it yields Lemma 2.4(i).
--
--   **Formalization Note** "Nondecreasing entries" is `Monotone` on `Fin n`.
--
--   Differences from the source: none.
-- source:
--   Yang, Chen & Xiang, Sparse solutions of a class of constrained optimization problems, arXiv:1907.00880v5, p. 8, Lemma 2.3; proof Appendix A, p. 23

import Mathlib
import Definitions.Def_SparseLpLq_SmallP_Setting

open scoped ENNReal Matrix

namespace SparseLpLq.SmallP
theorem lemma_2_3 {n : ℕ} (a b : Fin n → ℝ) (ha : Monotone a) (hb : Monotone b)
    (h : ∀ k ∈ Finset.Icc 1 n, ∑ j, a j ^ k = ∑ j, b j ^ k) :
    a = b := by sorry
end SparseLpLq.SmallP
