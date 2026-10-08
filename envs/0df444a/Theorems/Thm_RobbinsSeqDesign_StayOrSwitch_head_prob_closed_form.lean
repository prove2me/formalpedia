-- Prove2me | Theorems.Thm_RobbinsSeqDesign_StayOrSwitch_head_prob_closed_form
-- name    : RobbinsSeqDesign.StayOrSwitch.head_prob_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:04.29236+00:00
-- url     : https://prove2.me/theorems/1a2e88e9-e8f7-4d23-be16-0ad6983aff1c
-- title:
--   Section 2, Eq. (3) — closed form of p_i under R₁
-- statement:
--   Let coins $A$ and $B$ have head probabilities $\alpha, \beta\in[0,1]$, not both $0$ and not both $1$, and let $p_i$ be the probability of heads on the $i$-th toss under the rule $R_1$. Then $\alpha+\beta \neq 2$, and for every $i\ge1$,
--
--   $$
--   p_i = (\alpha+\beta-1)^{\,i-1}\left[p_1 - \frac{\alpha+\beta-2\alpha\beta}{2-(\alpha+\beta)}\right] + \frac{\alpha+\beta-2\alpha\beta}{2-(\alpha+\beta)} .
--   $$
--
--   Since $|\alpha+\beta-1|<1$ under the hypothesis, the first term decays geometrically; this gives the limit (4).
--
--   **Formalization Note** The exclusion "not both $0$ or both $1$" is the paper's standing hypothesis stated just before (2); it makes the denominator positive. At $i = 1$ the power is $0^0 = 1$ when $\alpha+\beta = 1$, which is the reading the formula needs.
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), p. 530, Section 2, Eq. (3)

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Rules

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsSeqDesign.StayOrSwitch

/-- Section 2, Eq. (3), p. 530: if `α, β` are not both `0` and not both `1`, then under rule
`R₁`, for every `i ≥ 1`,
`p_i = (α + β − 1)^{i−1} [p₁ − (α + β − 2αβ)/(2 − (α + β))] + (α + β − 2αβ)/(2 − (α + β))`. -/
theorem head_prob_closed_form (α β : unitInterval)
    (hnot0 : ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0)) (hnot1 : ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1))
    (i : ℕ) (hi : 1 ≤ i) :
    headProb ruleR1 α β i =
      ((α : ℝ) + β - 1) ^ (i - 1) *
          (headProb ruleR1 α β 1 - ((α : ℝ) + β - 2 * α * β) / (2 - ((α : ℝ) + β))) +
        ((α : ℝ) + β - 2 * α * β) / (2 - ((α : ℝ) + β)) := by sorry

end RobbinsSeqDesign.StayOrSwitch
