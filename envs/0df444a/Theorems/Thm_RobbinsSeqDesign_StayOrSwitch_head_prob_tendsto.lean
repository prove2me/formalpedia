-- Prove2me | Theorems.Thm_RobbinsSeqDesign_StayOrSwitch_head_prob_tendsto
-- name    : RobbinsSeqDesign.StayOrSwitch.head_prob_tendsto
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:02.352991+00:00
-- url     : https://prove2.me/theorems/d637d6cb-297d-4a23-adfa-d88e789401ef
-- title:
--   Section 2, Eqs. (4)–(5) — lim p_i = (α+β−2αβ)/(2−(α+β)) = γ + δ²/(1−γ) under R₁
-- statement:
--   Let coins $A$ and $B$ have head probabilities $\alpha, \beta\in[0,1]$, not both $0$ and not both $1$, let $p_i$ be the probability of heads on the $i$-th toss under the rule $R_1$, and let $\gamma = (\alpha+\beta)/2$, $\delta = |\alpha-\beta|/2$ as in (5). Then
--
--   $$
--   \lim_{i\to\infty} p_i = \frac{\alpha+\beta-2\alpha\beta}{2-(\alpha+\beta)} = \gamma + \frac{\delta^2}{1-\gamma}.
--   $$
--
--   The limit is the long-run frequency of heads under $R_1$, the quantity the asymptotic loss (8) is computed from.
--
--   **Formalization Note** The statement is the conjunction of the convergence and of the identity of the two closed forms. Both denominators are positive under the exclusion.
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), pp. 530–531, Section 2, Eqs. (4) and (5)

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Rules

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsSeqDesign.StayOrSwitch

/-- Section 2, Eqs. (4)–(5), pp. 530–531: if `α, β` are not both `0` and not both `1`, then
under rule `R₁`, `lim_{i→∞} p_i = (α + β − 2αβ)/(2 − (α + β)) = γ + δ²/(1 − γ)`. -/
theorem head_prob_tendsto (α β : unitInterval)
    (hnot0 : ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0)) (hnot1 : ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1)) :
    Tendsto (fun i => headProb ruleR1 α β i) atTop
        (𝓝 (((α : ℝ) + β - 2 * α * β) / (2 - ((α : ℝ) + β)))) ∧
      ((α : ℝ) + β - 2 * α * β) / (2 - ((α : ℝ) + β)) =
        gamma α β + delta α β ^ 2 / (1 - gamma α β) := by sorry

end RobbinsSeqDesign.StayOrSwitch
