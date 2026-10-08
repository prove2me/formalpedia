-- Prove2me | Theorems.Thm_PiIrrationality_ZZEven_coef_le
-- name    : PiIrrationality.ZZEven.coef_le
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T09:46:28.215706+00:00
-- url     : https://prove2.me/theorems/81ddea1a-eb51-4dbc-92cc-01f9e551241b
-- title:
--   Upper bound $\mathrm{coef}_n\le e^{17.22n}$ for the positive Zeilberger–Zudilin coefficient
-- statement:
--   For every $n\ge0$,
--   $$
--   \mathrm{coef}_n=[z^{6n}]\,\frac{\bigl((1+z)^4(2+6z+9z^2+6z^3+2z^4)^4\bigr)^n}{(1-z)^{8n}}\ \le\ e^{17.22\,n}.
--   $$
--
--   Write $S(z)=(1+z)^4(2+6z+9z^2+6z^3+2z^4)^4/(1-z)^8$. All coefficients of $S$ are nonnegative, so $[z^{6n}]S(z)^n\le S(x)^n x^{-6n}$ for every $0<x<1$. The minimum of $\log S(x)-6\log x$ is $17.21147\ldots$, attained at $x=0.2392\ldots$. This is the exponential growth rate of the $\pi$-coefficient of the even-index Zeilberger–Zudilin forms, after removing the factor $16^n$.
-- source:
--   Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), Section 4.1, equations (4.1)–(4.5) and Proposition 4.2 (positive-coefficient extraction), specialised to (a,b,c)=(2,4,6); D. Zeilberger and W. Zudilin, The irrationality measure of π is at most 7.103205334137…, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419, arXiv:1912.06345, Proposition 2 (lim b_n^(1/n) = N3).

import Definitions.Def_PiIrrationality_ZZEvenForms
import Mathlib.Analysis.SpecialFunctions.Exp

theorem PiIrrationality.ZZEven.coef_le (n : ℕ) :
    (PiIrrationality.ZZEven.coef n : ℝ) ≤ Real.exp (1722 / 100 * (n : ℝ)) := by
  sorry
