-- Prove2me | Theorems.Thm_PiIrrationality_lcmUpto_le_exp
-- name    : PiIrrationality.lcmUpto_le_exp
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T09:28:51.579806+00:00
-- url     : https://prove2.me/theorems/ced40b41-4c37-4a4e-93a3-ab07817a7189
-- title:
--   $\operatorname{lcm}(1,\dots,m)\le e^{(1+\delta)m}$ for all large $m$
-- statement:
--   For every $\delta>0$ there is $m_0$ such that
--   $$
--   \operatorname{lcm}(1,2,\dots,m)\ \le\ e^{(1+\delta)m}\qquad (m\ge m_0).
--   $$
--
--   Since $\log\operatorname{lcm}(1,\dots,m)=\psi(m)$, this is the upper half of the prime number theorem $\psi(x)\sim x$. It is the standard estimate for the common denominators of linear forms built from rational functions with poles of bounded order.
-- source:
--   Hardy–Wright, An Introduction to the Theory of Numbers, Thm. 6 and §22.2 (ψ(x) = log lcm(1..x), ψ(x) ~ x); used in D. Zeilberger and W. Zudilin, The irrationality measure of π is at most 7.103205334137…, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419, arXiv:1912.06345, World record paragraph.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Basic

theorem PiIrrationality.lcmUpto_le_exp (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in Filter.atTop, (Nat.lcmUpto m : ℝ) ≤ Real.exp ((1 + δ) * (m : ℝ)) := by
  sorry
