-- Prove2me | Theorems.Thm_WassTwoStage_Copositive_theorem_3
-- name    : WassTwoStage.Copositive.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:59:17.880761+00:00
-- url     : https://prove2.me/theorems/7f485434-d0c0-482b-955e-45b59ac7a359
-- title:
--   Theorem 3 — the completely positive program (14) equals the worst-case expectation
-- statement:
--   Assume the setting of §3 ($\Xi \ne \emptyset$, sufficiently expensive recourse, $I\ge1$, $\hat\xi_i\in\Xi$, $\epsilon\ge0$). For every first-stage decision $x$,
--   $$\mathcal Z(x) = \underline{\mathcal Z}(x),$$
--   where $\underline{\mathcal Z}(x)$ is the optimal value of the completely positive program (14).
--
--   This is the exact completely positive reformulation of the worst-case expected recourse cost; together with Proposition 1 it gives $\mathcal Z(x) = \underline{\mathcal Z}(x) \le \overline{\mathcal Z}(x)$.
--
--   **Formalization Note** "For any fixed $x\in\mathcal X$" is stated for every $x \in \mathbb R^{N_1}$. Both sides are extended reals; under the hypotheses $\mathcal Z(x) > -\infty$, while $+\infty$ is possible.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 10, Theorem 3; proof pp. 10–13

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_ConicPrograms

namespace WassTwoStage.Copositive

/-- Theorem 3 (completely positive reformulation), Hanasusanto–Kuhn, arXiv:1609.07505v3, p. 10
(proof pp. 10–13): under the standing assumptions of §3, for every first-stage decision `x` the
worst-case expectation `𝒵(x)` of (2) equals the optimal value `𝒵̲(x) = 𝒵̲_0(x)` of the
completely positive program (14). -/
theorem theorem_3 {K J M N₁ N₂ I : ℕ} (d : Data K J M N₁ N₂ I) (hI : 0 < I)
    (hXi : d.Xi.Nonempty) (hSER : d.SufficientlyExpensiveRecourse)
    (hξ : ∀ i, d.ξhat i ∈ d.Xi) (hε : 0 ≤ d.ε) (x : Fin N₁ → ℝ) :
    d.worstCase x = d.lowerValue 0 x := by sorry

end WassTwoStage.Copositive
