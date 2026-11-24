-- Prove2me | Theorems.Thm_SchoenfeldBRH_psi_bound_finite_range
-- name    : SchoenfeldBRH.psi_bound_finite_range
-- status  : Open
-- author  : @xuanji
-- created : 2026-11-24T02:19:59.495056+00:00
-- url     : https://prove2.me/theorems/18bf014b-f944-431f-b85b-43baa6ccd2c9
-- title:
--   Schoenfeld's $\psi$ bound on the finite range $73.2\le x\le e^{13}$
-- statement:
--   Let $\psi(x)=\sum_{p^m\le x}\log p$ be Chebyshev's function. For every real $x$ with $73.2\le x\le e^{13}\approx 442413.4$,
--   $$|\psi(x)-x|<\frac{\sqrt{x}\,\log^2 x}{8\pi}.$$
--
--   This is an unconditional finite computation: $\psi$ is a step function, so it suffices to compare the values $\psi(n)$, $n\le 442414$, with the increasing right-hand side at the endpoints of each unit interval. The smallest margin occurs near $x=96$ and equals about $0.59$.
-- source:
--   L. Schoenfeld, Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II, Math. Comp. 30 (1976), 337–360, Theorem 10 (6.3), finite range verified numerically there.

import Mathlib

theorem SchoenfeldBRH.psi_bound_finite_range :
    ∀ x : ℝ, (73.2 : ℝ) ≤ x → x ≤ Real.exp 13 →
      |Chebyshev.psi x - x| < Real.sqrt x * (Real.log x) ^ 2 / (8 * Real.pi) := by sorry
