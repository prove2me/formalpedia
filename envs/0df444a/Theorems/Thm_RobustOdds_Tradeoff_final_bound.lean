-- Prove2me | Theorems.Thm_RobustOdds_Tradeoff_final_bound
-- name    : RobustOdds.Tradeoff.final_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:12.99636+00:00
-- url     : https://prove2.me/theorems/94bb1ee4-765a-45a6-a0ba-dfa36ceb8b42
-- title:
--   App. C, p. 16 — 1 − ½(pa + (1 − p)b) ≥ 1 − δ, a ≥ 0, ½ ≤ p < 1 imply ½((1 − p)a + pb) ≤ (p/(1 − p))δ
-- statement:
--   Let $p, a, b, \delta \in \mathbb R$ with $\tfrac12 \le p < 1$ and $a \ge 0$. If
--
--   $$ 1 - \tfrac12\big(pa + (1-p)b\big) \ge 1 - \delta, $$
--
--   then
--
--   $$ \tfrac12\big((1-p)a + pb\big) \le \frac{p}{1-p}\,\delta. $$
--
--   In the proof of Theorem 2.1, $a = 1 - p_{++} + p_{--}$ and $b = 1 - p_{-+} + p_{+-}$; the left side of the hypothesis is the standard accuracy and the left side of the conclusion is the accuracy against the shift adversary. The paper's "since $p_{ij}$ are probabilities, we can guarantee that $a \ge 0$" is the hypothesis $a \ge 0$. This is the closing algebraic step of the proof.
-- source:
--   Tsipras et al., Robustness May Be at Odds with Accuracy, arXiv:1805.12152v5, p. 16, App. C, proof of Theorem 2.1, last two displays

import Mathlib
import Definitions.Def_RobustOdds_Tradeoff_Setting

namespace RobustOdds.Tradeoff

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- App. C, p. 16: with `a = 1 − p₊₊ + p₋₋ ≥ 0` and `b = 1 − p₋₊ + p₊₋`, standard accuracy
`1 − ½(pa + (1 − p)b) ≥ 1 − δ` and `½ ≤ p < 1` give adversarial accuracy `½((1 − p)a + pb) ≤ (p/(1 − p))δ`. -/
theorem final_bound :
    ∀ p a b δ : ℝ, 1 / 2 ≤ p → p < 1 → 0 ≤ a →
      1 - δ ≤ 1 - 1 / 2 * (p * a + (1 - p) * b) →
      1 / 2 * ((1 - p) * a + p * b) ≤ p / (1 - p) * δ := by sorry
end RobustOdds.Tradeoff
