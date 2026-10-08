-- Prove2me | Theorems.Thm_PiIrrationality_ZZEven_integral_bound
-- name    : PiIrrationality.ZZEven.integral_bound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T09:46:19.441307+00:00
-- url     : https://prove2.me/theorems/31653b1c-aab5-4068-9727-3f81c355fcc0
-- title:
--   Explicit exponential decay $|J_n|\le 10e^{-7n}$ of the even-index Zeilberger–Zudilin integrals
-- statement:
--   For every $n\ge 0$,
--   $$
--   |J_n|\ \le\ 10\,e^{-7n},
--   $$
--   where $J_n=i\int_{-1-2i}^{-1+2i}R_n(t)\,dt$ and $R_n(t)=5t^{4n}(t^4+6t^2+25)^{4n}(25-t^2)^{-6n-1}$, as in the definition file `PiIrrationality_ZZEvenForms`.
--
--   Zeilberger and Zudilin show $\limsup|I_m|^{1/m}=|N_1|=0.02945849\ldots$ for their integrals $I_m$. At even index $m=2n$ the true rate is $|N_1|^2=0.000867803\ldots<e^{-7}=0.000911882\ldots$. The rate is attained along a contour inside the disc $|t|<5$ that passes through the saddle points of $|t|^4|t^4+6t^2+25|^4/|25-t^2|^6$. The statement is an explicit, slightly weaker form with a uniform constant.
-- source:
--   D. Zeilberger and W. Zudilin, The irrationality measure of π is at most 7.103205334137…, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419, arXiv:1912.06345, Proposition 2 (limsup |I_n|^(1/n) = |N1| = 0.029458495928…); Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), Section 4.2–4.3, Lemma 4.4 and Proposition 4.5.

import Definitions.Def_PiIrrationality_ZZEvenForms
import Mathlib.Analysis.SpecialFunctions.Exp

theorem PiIrrationality.ZZEven.integral_bound (n : ℕ) :
    ‖PiIrrationality.ZZEven.J n‖ ≤ 10 * Real.exp (-(7 * (n : ℝ))) := by
  sorry
