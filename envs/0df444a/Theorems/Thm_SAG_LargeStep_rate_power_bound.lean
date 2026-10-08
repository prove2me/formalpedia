-- Prove2me | Theorems.Thm_SAG_LargeStep_rate_power_bound
-- name    : SAG.LargeStep.rate_power_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:15.285975+00:00
-- url     : https://prove2.me/theorems/7b118d94-31fb-42da-9e3d-d8105b332b63
-- title:
--   §A.6 Step 3 — (1 − 1/(8n))^{−n} ≤ 8/7
-- statement:
--   For every integer $n\ge1$,
--   $$\Big(1-\frac1{8n}\Big)^{-n}\le\frac87 .$$
--
--   This converts the factor $(1-\frac1{8n})^{k-n}$, which arises because the first $n$ iterations are spent on stochastic gradient, into $(1-\frac1{8n})^k$ in Proposition 2.
-- source:
--   Le Roux, Schmidt & Bach, A Stochastic Gradient Method with an Exponential Convergence Rate for Finite Training Sets, arXiv:1202.6258v4, p. 30, §A.6 Step 3

import Mathlib

namespace SAG.LargeStep

/-- §A.6 Step 3, p. 30: `(1 − 1/(8n))^{−n} ≤ 8/7` for every `n ≥ 1`. -/
theorem rate_power_bound (n : ℕ) (hn : 0 < n) :
    (1 - 1 / (8 * (n : ℝ))) ^ (-(n : ℤ)) ≤ 8 / 7 := by sorry

end SAG.LargeStep
