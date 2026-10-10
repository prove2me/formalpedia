-- Prove2me | Theorems.Thm_StrongWeakEq_TwoState_display_4_12
-- name    : StrongWeakEq.TwoState.display_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:34:46.332913+00:00
-- url     : https://prove2.me/theorems/a2374fda-6fb7-4a26-991e-2b50ae2b1a92
-- title:
--   (4.12), p. 13 — Λ₂(a*, b) = −b/12 − 579/288 on [0, 7/12], so Λ₂(a*, b*) < Λ₂(a*, b) for b ∈ [0, 7/12)
-- statement:
--   In Example 4.3 let $Q^*\sim(a^*,b^*)=(5/12,7/12)$, let $f_t=\delta'(t)g$ be the time derivative of the example's payoff, and for $Q\sim(a^*,b)$ write $\Lambda^{(a^*,b^*)}_2(a^*,b)=\Lambda^{Q^*}(2,Q)$. Then
--   $$
--   \Lambda^{(a^*,b^*)}_2(a^*,b)=-\frac1{12}\,b-\frac{579}{288}\qquad\text{for }0\le b\le\frac7{12},
--   $$
--   and consequently
--   $$
--   \Lambda^{(a^*,b^*)}_2(a^*,b^*)<\Lambda^{(a^*,b^*)}_2(a^*,b)\qquad\forall b\in[0,7/12). \tag{4.12}
--   $$
--
--   Since $(2,Q)$ lies in the set $R$ of (3.22) for these $Q$, this is the input of Proposition 3.3 showing that $Q^*$ is not a strong equilibrium.
--
--   **Formalization Note** State 2 is `1 : Fin 2`; $Q^*$ itself is $Q\sim(a^*,b^*)$, so the left side of (4.12) is `Lambda ex43 ex43Deriv Qstar 1 Qstar`.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 13, Example 4.3, (4.12)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder
import Definitions.Def_StrongWeakEq_TwoState_TwoStateModel
import Definitions.Def_StrongWeakEq_TwoState_Example43

namespace StrongWeakEq.TwoState

/-- (4.12), p. 13, Example 4.3: `Λ₂(a*, b) = Λ^{Q*}(2, Q)` for `Q ∼ (5/12, b)` equals
`−b/12 − 579/288` for `0 ≤ b ≤ 7/12`, hence `Λ₂(a*, b*) < Λ₂(a*, b)` for every `b ∈ [0, 7/12)`. -/
theorem display_4_12 :
    (∀ b ∈ Set.Icc (0:ℝ) (7 / 12),
      StrongWeakEq.Existence.Lambda ex43 ex43Deriv Qstar 1 (gen (5 / 12) b) = -(1 / 12) * b - 579 / 288) ∧
    (∀ b ∈ Set.Ico (0:ℝ) (7 / 12),
      StrongWeakEq.Existence.Lambda ex43 ex43Deriv Qstar 1 Qstar < StrongWeakEq.Existence.Lambda ex43 ex43Deriv Qstar 1 (gen (5 / 12) b)) := by sorry

end StrongWeakEq.TwoState
