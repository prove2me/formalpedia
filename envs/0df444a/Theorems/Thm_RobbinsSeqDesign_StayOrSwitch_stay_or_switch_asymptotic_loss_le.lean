-- Prove2me | Theorems.Thm_RobbinsSeqDesign_StayOrSwitch_stay_or_switch_asymptotic_loss_le
-- name    : RobbinsSeqDesign.StayOrSwitch.stay_or_switch_asymptotic_loss_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:42:26.471983+00:00
-- url     : https://prove2.me/theorems/3af10f2f-8a38-4d29-b3a1-4a99f5b07fb2
-- title:
--   Section 2, Eqs. (6), (8) and M₁ — staying on heads and switching on tails loses at most 3 − 2^{3/2} per toss in the long run
-- statement:
--   Let coins $A$ and $B$ have head probabilities $\alpha,\beta\in[0,1]$, not both $0$ and not both $1$, put $\gamma = (\alpha+\beta)/2$, $\delta = |\alpha-\beta|/2$, and let $S_n$ be the total payoff of the first $n$ tosses under the rule $R_1$: toss a fairly chosen coin first, then keep the coin after a head and switch to the other coin after a tail. Then
--
--   1. $\displaystyle\lim_{n\to\infty}\mathrm E\!\left(\frac{S_n}{n}\right) = \gamma+\frac{\delta^2}{1-\gamma}$;
--   2. the loss per toss relative to always tossing the better coin converges to the asymptotic loss
--   $$
--   L(A,B,R_1) = \lim_{n\to\infty}\left[\max(\alpha,\beta)-\mathrm E\!\left(\frac{S_n}{n}\right)\right] = \delta\left[1-\frac{\delta}{1-\gamma}\right];
--   $$
--   3. $0 \le L(A,B,R_1) \le M_1 = 3-2^{3/2}$;
--   4. $L(A,B,R_1) = M_1$ when $\alpha = 0$, $\beta = 2-2^{1/2}$, and when $\alpha = 2-2^{1/2}$, $\beta = 0$.
--
--   So a person who uses $R_1$ loses in the long run at most $3-2^{3/2}\approx 0.172$ per toss, whatever the coins, against $1/2$ for a rule that ignores the outcomes.
--
--   **Formalization Note** The asymptotic loss is stated as the limit of $\max(\alpha,\beta) - \mathrm E(S_n/n)$, not defined by its closed form. $2^{3/2}$ is written `2 * Real.sqrt 2`. The head probabilities are elements of `unitInterval`; the attainment clause quantifies over the elements of `unitInterval` with the stated real values ($2-\sqrt2\in[0,1]$, so it is not vacuous).
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), p. 531, Section 2, Eqs. (6), (8) and the maximum M₁

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Rules

open MeasureTheory ProbabilityTheory Filter Topology

namespace RobbinsSeqDesign.StayOrSwitch

/-- Section 2, Eqs. (6), (8) and the maximum `M₁`, p. 531 (goal). For coins with head
probabilities `0 ≤ α, β ≤ 1`, not both `0` and not both `1`, under rule `R₁`:
`lim E(S_n/n) = γ + δ²/(1 − γ)`, the loss per toss `max(α, β) − E(S_n/n)` tends to
`L(A, B, R₁) = δ[1 − δ/(1 − γ)]`, and `0 ≤ L(A, B, R₁) ≤ M₁ = 3 − 2^{3/2}`, with
`L(A, B, R₁) = M₁` at `α = 0, β = 2 − 2^{1/2}` and at `α = 2 − 2^{1/2}, β = 0`. -/
theorem stay_or_switch_asymptotic_loss_le :
    (∀ α β : unitInterval, ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0) → ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1) →
        Tendsto (fun n => expectedAverage ruleR1 α β n) atTop
            (𝓝 (gamma α β + delta α β ^ 2 / (1 - gamma α β))) ∧
          Tendsto (fun n => max (α : ℝ) β - expectedAverage ruleR1 α β n) atTop
            (𝓝 (delta α β * (1 - delta α β / (1 - gamma α β)))) ∧
          0 ≤ delta α β * (1 - delta α β / (1 - gamma α β)) ∧
          delta α β * (1 - delta α β / (1 - gamma α β)) ≤ 3 - 2 * Real.sqrt 2) ∧
      (∀ α β : unitInterval,
        ((α : ℝ) = 0 ∧ (β : ℝ) = 2 - Real.sqrt 2) ∨ ((α : ℝ) = 2 - Real.sqrt 2 ∧ (β : ℝ) = 0) →
          Tendsto (fun n => max (α : ℝ) β - expectedAverage ruleR1 α β n) atTop
            (𝓝 (3 - 2 * Real.sqrt 2))) := by sorry

end RobbinsSeqDesign.StayOrSwitch
