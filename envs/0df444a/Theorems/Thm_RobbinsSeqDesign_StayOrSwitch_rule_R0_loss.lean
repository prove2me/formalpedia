-- Prove2me | Theorems.Thm_RobbinsSeqDesign_StayOrSwitch_rule_R0_loss
-- name    : RobbinsSeqDesign.StayOrSwitch.rule_R0_loss
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:13.264975+00:00
-- url     : https://prove2.me/theorems/f63424eb-513f-476b-bb7a-771d967db498
-- title:
--   Section 2, p. 531 — rule R₀ has asymptotic loss L(A, B, R₀) = δ, with maximum M₀ = 1/2 at (0, 1) and (1, 0)
-- statement:
--   Let coins $A$ and $B$ have head probabilities $\alpha,\beta\in[0,1]$, not both $0$ and not both $1$, and let $\gamma,\delta$ be as in (5). Under the rule $R_0$ (choose one of the coins at random and stick to it), the loss per toss tends to $\delta$:
--
--   $$
--   \lim_{n\to\infty}\left[\max(\alpha,\beta) - \mathrm E\!\left(\frac{S_n}{n}\right)\right] = L(A,B,R_0) = (\gamma+\delta)-\gamma = \delta .
--   $$
--
--   Moreover $\delta \le \tfrac12$ for every admissible $(\alpha,\beta)$, with $\delta = \tfrac12$ at $\alpha = 0,\beta = 1$ and at $\alpha = 1,\beta = 0$; so the worst case of $R_0$ is $M_0 = 1/2$, against $M_1 = 3-2^{3/2}$ for $R_1$.
--
--   **Formalization Note** "At random" is the fair choice. The paper's parenthetical alternative "(or in tossing the two coins alternately)" is not part of this statement. The standing exclusion of the two corners is kept, as on the page.
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), p. 531, Section 2 (rule R₀, L(A, B, R₀), M₀)

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Rules

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsSeqDesign.StayOrSwitch

/-- Section 2, p. 531, rule `R₀`: if `α, β` are not both `0` and not both `1`, the loss per toss
`max(α, β) − E(S_n/n)` of rule `R₀` tends to `L(A, B, R₀) = (γ + δ) − γ = δ`; and `δ` has the
maximum `M₀ = 1/2` over all admissible `(α, β)`, taken at `α = 0, β = 1` and at
`α = 1, β = 0`. -/
theorem rule_R0_loss :
    (∀ α β : unitInterval, ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0) → ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1) →
        Tendsto (fun n => max (α : ℝ) β - expectedAverage ruleR0 α β n) atTop
          (𝓝 (delta α β))) ∧
      (∀ α β : ℝ, 0 ≤ α → α ≤ 1 → 0 ≤ β → β ≤ 1 → ¬(α = 0 ∧ β = 0) → ¬(α = 1 ∧ β = 1) →
        delta α β ≤ 1 / 2) ∧
      delta 0 1 = 1 / 2 ∧ delta 1 0 = 1 / 2 := by sorry

end RobbinsSeqDesign.StayOrSwitch
