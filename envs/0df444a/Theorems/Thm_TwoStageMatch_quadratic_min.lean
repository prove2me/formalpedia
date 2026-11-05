-- Prove2me | Theorems.Thm_TwoStageMatch_quadratic_min
-- name    : TwoStageMatch.quadratic_min
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:29:54.829574+00:00
-- url     : https://prove2.me/theorems/2998c397-d291-4e21-bd97-2bd6af519155
-- title:
--   Step (3) of (6): $\min_{x\in[0,1]}1-x+x^2=3/4$
-- statement:
--   For every $x\in[0,1]$,
--   $$1-x+x^2\ge\frac34,$$
--   with equality at $x=\tfrac12\in[0,1]$; hence $\min_{x\in[0,1]}1-x+x^2=\tfrac34$.
--
--   This is the inequality behind both dual-feasibility estimates (6) and (7), applied to $x=y^*_j$, and the source of the constant $3/4$ in Theorem 1.
--
--   Differences from the source:
--   - encoding: min_{x∈[0,1]} 1 − x + x² = 3/4 → a lower bound 3/4 on [0, 1] together with its attainment at x = 1/2; reason: the two statements together are the value of the minimum
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, proof of Theorem 1, p.15, eq. (6), step (3)

import Mathlib

namespace TwoStageMatch

/-- **Step (3) of (6)** (Feng, Niazadeh & Saberi, arXiv:2210.11648v1, p.15: "(3) holds as
y*_j ∈ [0, 1], and min_{x ∈ [0,1]} 1 − x + x² = 3/4"). For every `x ∈ [0, 1]`,
`1 − x + x² ≥ 3/4`, with equality at `x = 1/2`; so the minimum over `[0, 1]` is `3/4`. -/
theorem quadratic_min :
    (∀ x ∈ Set.Icc (0 : ℝ) 1, (3 / 4 : ℝ) ≤ 1 - x + x ^ 2) ∧
    ((1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧ (1 : ℝ) - 1 / 2 + (1 / 2) ^ 2 = 3 / 4) := by sorry

end TwoStageMatch
