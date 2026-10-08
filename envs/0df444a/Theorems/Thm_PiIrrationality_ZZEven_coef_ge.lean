-- Prove2me | Theorems.Thm_PiIrrationality_ZZEven_coef_ge
-- name    : PiIrrationality.ZZEven.coef_ge
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T09:46:38.271523+00:00
-- url     : https://prove2.me/theorems/68710641-53bd-4620-be35-01fd6e33501e
-- title:
--   Lower bound $\mathrm{coef}_n\ge e^{17.20n}$ for large $n$
-- statement:
--   There is $N$ such that for all $n\ge N$,
--   $$
--   e^{17.20\,n}\ \le\ \mathrm{coef}_n=[z^{6n}]\,\frac{\bigl((1+z)^4(2+6z+9z^2+6z^3+2z^4)^4\bigr)^n}{(1-z)^{8n}} .
--   $$
--
--   The exact growth rate is $\lim_n\frac1n\log\mathrm{coef}_n=\min_{0<x<1}\bigl(\log S(x)-6\log x\bigr)=17.21147\ldots$, where $S(z)=(1+z)^4(2+6z+9z^2+6z^3+2z^4)^4/(1-z)^8$ has positive coefficients. Together with the upper bound $e^{17.22n}$, this lower bound controls the ratio between the linear form and its $\pi$-coefficient, which is what the index-selection argument needs.
-- source:
--   Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), Section 4.1, Lemma 4.1 and Proposition 4.2 (ordinary limit of the coefficient rate), specialised to (a,b,c)=(2,4,6).

import Definitions.Def_PiIrrationality_ZZEvenForms
import Mathlib.Analysis.SpecialFunctions.Exp

theorem PiIrrationality.ZZEven.coef_ge :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.exp (1720 / 100 * (n : ℝ)) ≤ (PiIrrationality.ZZEven.coef n : ℝ) := by
  sorry
