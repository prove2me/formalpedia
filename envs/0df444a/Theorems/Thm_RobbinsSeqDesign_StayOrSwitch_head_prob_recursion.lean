-- Prove2me | Theorems.Thm_RobbinsSeqDesign_StayOrSwitch_head_prob_recursion
-- name    : RobbinsSeqDesign.StayOrSwitch.head_prob_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:41:53.308686+00:00
-- url     : https://prove2.me/theorems/c7e8b16e-d416-461e-ba74-1c6ad81cb199
-- title:
--   Section 2, Eq. (2) — p_{i+1} = (α+β−1)p_i + (α+β−2αβ) under R₁
-- statement:
--   Let coins $A$ and $B$ have head probabilities $\alpha, \beta\in[0,1]$, not both $0$ and not both $1$, and let $p_i$ be the probability of heads on the $i$-th toss when the rule $R_1$ (stay on heads, switch on tails, fair first choice) is used. Then for every $i \ge 1$,
--
--   $$
--   p_{i+1} = (\alpha+\beta-1)\,p_i + (\alpha+\beta-2\alpha\beta).
--   $$
--
--   This affine recursion is the operating characteristic of $R_1$ from which the closed form (3) and the limits (4) and (6) follow.
--
--   **Formalization Note** The two excluded corners are the standing hypothesis stated immediately before Eq. (2). Tosses are indexed from $1$.
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), p. 530, Section 2, Eq. (2)

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Rules

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsSeqDesign.StayOrSwitch

/-- Section 2, Eq. (2), p. 530: under rule `R₁`, when `α, β` are not both `0` and not both
`1`, for every `i ≥ 1`,
`p_{i+1} = (α + β − 1) p_i + (α + β − 2αβ)`. -/
theorem head_prob_recursion (α β : unitInterval)
    (hnot0 : ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0)) (hnot1 : ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1))
    (i : ℕ) (hi : 1 ≤ i) :
    headProb ruleR1 α β (i + 1) =
      ((α : ℝ) + β - 1) * headProb ruleR1 α β i + ((α : ℝ) + β - 2 * α * β) := by sorry

end RobbinsSeqDesign.StayOrSwitch
