-- Prove2me | Theorems.Thm_ResolvingNRM_FRLower_q3_probability
-- name    : ResolvingNRM.FRLower.q3_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:18:27.050834+00:00
-- url     : https://prove2.me/theorems/f34a8bef-e159-41af-9e42-bff63ea91ec0
-- title:
--   Lemma 7, p. 40 — lower bound for the third-phase Poisson event
-- statement:
--   Let $T'\ge1$ be an integer and let $N$ have the Poisson distribution with mean $T'$. With $\Phi$ denoting the standard normal cumulative distribution function, the third-phase event $Q_3$ obeys
--
--   $$
--   \mathbb P\bigl(T'+6\sqrt{T'}\le N\le T'+7\sqrt{T'}\bigr)
--   \ge \Phi(7)-\Phi(6)-\frac{0.9496}{\sqrt{T'}}.
--   $$
--
--   This is the second separated Poisson event used to establish a positive-probability loss scenario.
--
--   **Formalization Note** Equation (52) proves the displayed unrounded Gaussian-tail constant. Equation (53) and the Lemma 7 headline round $\Phi(7)-\Phi(6)\approx9.85308\times10^{-10}$ upward to $9.8531\times10^{-10}$; the formal statement retains the proved value. The phase length is integral as in the proof.
-- source:
--   Bumpensanti, Wang, A Re-solving Heuristic with Uniformly Bounded Loss for Network Revenue Management, arXiv:1802.06192v3, Lemma 7, p. 40, Q3 clause and (52)–(53)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ResolvingNRM.FRLower

/-- The Q₃ component of Lemma 7 in its proved, unrounded form (52). -/
theorem q3_probability (T' : ℕ) (hT : 1 ≤ T') :
    (∑' k : ℕ, if (T' : ℝ) + 6 * Real.sqrt (T' : ℝ) ≤ (k : ℝ) ∧
        (k : ℝ) ≤ (T' : ℝ) + 7 * Real.sqrt (T' : ℝ) then
        ProbabilityTheory.poissonPMFReal (T' : ℝ).toNNReal k else (0 : ℝ)) ≥
      cdf (gaussianReal 0 1) 7 - cdf (gaussianReal 0 1) 6 -
        0.9496 / Real.sqrt (T' : ℝ) := by sorry

end ResolvingNRM.FRLower
