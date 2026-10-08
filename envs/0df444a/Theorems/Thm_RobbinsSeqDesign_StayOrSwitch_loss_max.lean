-- Prove2me | Theorems.Thm_RobbinsSeqDesign_StayOrSwitch_loss_max
-- name    : RobbinsSeqDesign.StayOrSwitch.loss_max
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:39:00.453398+00:00
-- url     : https://prove2.me/theorems/dec8ffb1-f370-4008-9b94-41005a9b3171
-- title:
--   Section 2, Eqs. (7)–(8) and M₁ — 0 ≤ δ[1 − δ/(1−γ)] ≤ 3 − 2^{3/2}, attained at (0, 2 − √2) and (2 − √2, 0)
-- statement:
--   For real numbers $0\le\alpha,\beta\le1$, not both $0$ and not both $1$, put $\gamma = (\alpha+\beta)/2$ and $\delta = |\alpha-\beta|/2$. Then
--
--   1. $\max(\alpha,\beta) = \gamma+\delta$;
--   2. the quantity $L(\alpha,\beta) = \delta\left[1 - \dfrac{\delta}{1-\gamma}\right]$ satisfies
--   $$
--   0 \le \delta\left[1-\frac{\delta}{1-\gamma}\right] \le 3 - 2^{3/2};
--   $$
--   3. the value $M_1 = 3-2^{3/2}$ is taken at $\alpha = 0$, $\beta = 2-2^{1/2}$ and at $\alpha = 2 - 2^{1/2}$, $\beta = 0$.
--
--   This is the elementary half of the paper's comparison: $L$ is the asymptotic loss per toss of the rule $R_1$, and $M_1 \approx 0.172$ is its worst case over all pairs of coins.
--
--   **Formalization Note** No probability enters this statement. $2^{3/2}$ is written as `2 * Real.sqrt 2`. The numerical values $\approx .172$ and $\approx .586$ are not formalized.
-- source:
--   Robbins, Some aspects of the sequential design of experiments, Bull. Amer. Math. Soc. 58 (1952), p. 531, Section 2, Eqs. (7), (8) and the maximum M₁

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Coins

namespace RobbinsSeqDesign.StayOrSwitch

/-- Section 2, Eqs. (7)–(8) and the maximum `M₁`, p. 531: for `0 ≤ α, β ≤ 1` not both `0` and
not both `1`, `max(α, β) = γ + δ` and `0 ≤ δ[1 − δ/(1 − γ)] ≤ 3 − 2^{3/2}`; the value
`3 − 2^{3/2}` is taken at `α = 0, β = 2 − 2^{1/2}` and at `α = 2 − 2^{1/2}, β = 0`. -/
theorem loss_max :
    (∀ α β : ℝ, 0 ≤ α → α ≤ 1 → 0 ≤ β → β ≤ 1 → ¬(α = 0 ∧ β = 0) → ¬(α = 1 ∧ β = 1) →
        max α β = gamma α β + delta α β ∧
          0 ≤ delta α β * (1 - delta α β / (1 - gamma α β)) ∧
          delta α β * (1 - delta α β / (1 - gamma α β)) ≤ 3 - 2 * Real.sqrt 2) ∧
      delta 0 (2 - Real.sqrt 2) * (1 - delta 0 (2 - Real.sqrt 2) / (1 - gamma 0 (2 - Real.sqrt 2)))
        = 3 - 2 * Real.sqrt 2 ∧
      delta (2 - Real.sqrt 2) 0 * (1 - delta (2 - Real.sqrt 2) 0 / (1 - gamma (2 - Real.sqrt 2) 0))
        = 3 - 2 * Real.sqrt 2 := by sorry

end RobbinsSeqDesign.StayOrSwitch
