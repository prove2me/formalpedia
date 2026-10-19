-- Prove2me | Theorems.Thm_Polynomial_isSumSq_of_eval_nonneg
-- name    : Polynomial.isSumSq_of_eval_nonneg
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T22:12:53.630718+00:00
-- url     : https://prove2.me/theorems/e04d8dde-f28a-4c30-83af-3599fd916ff8
-- title:
--   A real polynomial nonnegative everywhere is a sum of squares
-- statement:
--   Let $p\in\mathbb R[x]$ satisfy $p(t)\ge0$ for every real number $t$. Then $p$ is a finite sum of squares of real polynomials:
--
--   $$
--   p=q_1^2+\cdots+q_r^2\qquad(q_1,\ldots,q_r\in\mathbb R[x]).
--   $$
--
--   Together with the elementary reverse implication, this identifies the cone of nonnegative real univariate polynomials with the cone of sums of squares. It is the algebraic input that converts positivity of a Hankel quadratic form into the positivity hypothesis of the measure-representation theorem.
--
--   **Formalization Note** The conclusion uses Mathlib's inductively defined predicate `IsSumSq`. The zero polynomial is included.
-- source:
--   Konrad Schmüdgen, Ten Lectures on the Moment Problem (2020), arXiv:2008.12698v1, Proposition 1.10(i) and factorization (1.5), printed p.13 (PDF p.13). https://arxiv.org/pdf/2008.12698v1

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Ring.SumsOfSquares

set_option autoImplicit false

theorem Polynomial.isSumSq_of_eval_nonneg (p : Polynomial ℝ)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) : IsSumSq p := by sorry
