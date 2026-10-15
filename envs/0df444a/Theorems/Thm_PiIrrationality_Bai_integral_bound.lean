-- Prove2me | Theorems.Thm_PiIrrationality_Bai_integral_bound
-- name    : PiIrrationality.Bai.integral_bound
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-14T19:55:34.236367+00:00
-- url     : https://prove2.me/theorems/f2c327ec-b710-4ecf-86e2-5b985fbbb7c3
-- title:
--   Decay of Bai's integral: $\|J_n\|\le 2e^{-6542.209753096835\,n}$
-- statement:
--   For every $n$,
--   $$|J_n|\le 2\exp(-6542.209753096835\,n).$$
--
--   Role: the decay rate $T$ of the linear form; $T/5570$ is Bai's integral rate $-s$ of Proposition 4.5 up to $10^{-15}$.
-- source:
--   Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), https://arxiv.org/abs/2609.11276, Proposition 4.5 and (4.20)-(4.21)

import Definitions.Def_PiIrrationality_BaiForms
import Mathlib.Analysis.SpecialFunctions.Exp

theorem PiIrrationality.Bai.integral_bound (n : ℕ) :
    ‖PiIrrationality.Bai.J n‖ ≤ 2 * Real.exp (-(6542.209753096835 * (n : ℝ))) := by
  sorry
