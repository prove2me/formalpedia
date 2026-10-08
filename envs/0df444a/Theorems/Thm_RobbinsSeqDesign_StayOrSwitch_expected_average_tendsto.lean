-- Prove2me | Theorems.Thm_RobbinsSeqDesign_StayOrSwitch_expected_average_tendsto
-- name    : RobbinsSeqDesign.StayOrSwitch.expected_average_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:15.710407+00:00
-- url     : https://prove2.me/theorems/84a392e4-38c8-4312-9970-a66b46c72c7a
-- title:
--   Section 2, Eq. (6) — both E(S_n/n) and (p₁+⋯+p_n)/n tend to γ + δ²/(1−γ) under R₁
-- statement:
--   Let coins $A$ and $B$ have head probabilities $\alpha, \beta\in[0,1]$, not both $0$ and not both $1$; let $x_i\in\{0,1\}$ be the payoff of the $i$-th toss under the rule $R_1$, $S_n = x_1+\dots+x_n$, $p_i$ the probability of heads on the $i$-th toss, and $\gamma,\delta$ as in (5). Then
--
--   $$
--   \lim_{n\to\infty}\mathrm E\!\left(\frac{S_n}{n}\right)
--   = \lim_{n\to\infty}\frac{p_1+\dots+p_n}{n}
--   = \gamma + \frac{\delta^2}{1-\gamma}.
--   $$
--
--   This is the long-run expected payoff per toss of a person who uses $R_1$.
--
--   **Formalization Note** The Lean states both limits explicitly. The expectation is a Bochner integral of the average payoff over the trajectory law.
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), p. 531, Section 2, Eq. (6)

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Rules

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsSeqDesign.StayOrSwitch

/-- Section 2, Eq. (6), p. 531: if `α, β` are not both `0` and not both `1`, then under rule
`R₁`, both `E(S_n/n)` and `(p₁ + ⋯ + p_n)/n` tend to
`γ + δ²/(1 − γ)`. -/
theorem expected_average_tendsto (α β : unitInterval)
    (hnot0 : ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0)) (hnot1 : ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1)) :
    Tendsto (fun n => expectedAverage ruleR1 α β n) atTop
        (𝓝 (gamma α β + delta α β ^ 2 / (1 - gamma α β))) ∧
      Tendsto (fun n => (∑ i ∈ Finset.Icc 1 n, headProb ruleR1 α β i) / n) atTop
        (𝓝 (gamma α β + delta α β ^ 2 / (1 - gamma α β))) := by sorry

end RobbinsSeqDesign.StayOrSwitch
