-- Prove2me | Theorems.Thm_SPHardness_FixedRecourse_eq_8
-- name    : SPHardness.FixedRecourse.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:41.331585+00:00
-- url     : https://prove2.me/theorems/ddb1814b-7228-480e-85e7-353763b103bb
-- title:
--   Equation (8), p. 7 — inclusion–exclusion formula for knapsack volume
-- statement:
--   For strictly positive weights $\alpha_1,\ldots,\alpha_k$ and $\beta\ge0$, the volume of $P(\alpha,\beta)$ satisfies
--   $$V(\alpha,\beta)=\frac{\sum_{S\subseteq\{1,\ldots,k\}}(-1)^{|S|}\max\{0,\beta-\sum_{j\in S}\alpha_j\}^{k}}{k!\prod_{j=1}^k\alpha_j}.$$
--   This closed form is the volume identity cited from Dyer and Frieze in the proof of Theorem 1. The positive-weight condition makes the displayed denominator nonzero.
-- source:
--   Hanasusanto, Kuhn & Wiesemann, A comment on "computational complexity of stochastic programming problems", Optimization Online preprint 2015/03/4825 (version of October 6, 2015), p. 7, (8)

import Mathlib
import Definitions.Def_SPHardness_FixedRecourse_Model

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace SPHardness.FixedRecourse

theorem eq_8 {k : ℕ} (α : Fin k → ℝ) (β : ℝ)
    (hα : ∀ j, 0 < α j) (hβ : 0 ≤ β) :
    vol α β =
      (∑ s : Finset (Fin k), (-1 : ℝ) ^ s.card *
        (max 0 (β - ∑ j ∈ s, α j)) ^ k) /
        ((k.factorial : ℝ) * ∏ j, α j) := by sorry
end SPHardness.FixedRecourse
