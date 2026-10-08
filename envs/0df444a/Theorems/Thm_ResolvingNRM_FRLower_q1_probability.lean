-- Prove2me | Theorems.Thm_ResolvingNRM_FRLower_q1_probability
-- name    : ResolvingNRM.FRLower.q1_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:18:09.864346+00:00
-- url     : https://prove2.me/theorems/04d1791a-1a01-41d7-b6c6-e016ac154da2
-- title:
--   Lemma 7, p. 40 — lower bound for the first-phase Poisson event
-- statement:
--   Let $T'\ge1$ be an integer. For a Poisson random variable $N$ of mean $T'$, the first-phase event $Q_1$ has probability bounded below by
--
--   $$
--   \mathbb P\bigl(T'-4\sqrt{T'}\le N\le T'-3\sqrt{T'}\bigr)
--   \ge 0.0013-\frac{0.9496}{\sqrt{T'}}.
--   $$
--
--   This is the first marginal event probability used in the lower-bound construction.
--
--   **Formalization Note** The proof on p. 40 decomposes the Poisson count into $T'$ independent unit-time increments, so this item takes an integer phase length. The probability is an infinite sum of Poisson masses over the inclusive interval.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Lemma 7, p. 40, Q1 clause and (49)–(51)

import Mathlib

namespace ResolvingNRM.FRLower

/-- The Q₁ component of Lemma 7, with integer phase length as in the proof on p. 40. -/
theorem q1_probability (T' : ℕ) (hT : 1 ≤ T') :
    (∑' k : ℕ, if (T' : ℝ) - 4 * Real.sqrt (T' : ℝ) ≤ (k : ℝ) ∧
        (k : ℝ) ≤ (T' : ℝ) - 3 * Real.sqrt (T' : ℝ) then
        ProbabilityTheory.poissonPMFReal (T' : ℝ).toNNReal k else (0 : ℝ)) ≥
      0.0013 - 0.9496 / Real.sqrt (T' : ℝ) := by sorry

end ResolvingNRM.FRLower
