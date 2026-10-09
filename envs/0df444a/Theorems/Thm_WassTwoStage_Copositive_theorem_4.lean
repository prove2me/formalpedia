-- Prove2me | Theorems.Thm_WassTwoStage_Copositive_theorem_4
-- name    : WassTwoStage.Copositive.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:59:21.895912+00:00
-- url     : https://prove2.me/theorems/7ac10866-9a93-4c0e-908b-87e356ef9c0d
-- title:
--   Theorem 4 — under complete recourse, $\mathcal Z(x) = \underline{\mathcal Z}(x) = \overline{\mathcal Z}(x)$
-- statement:
--   Assume the setting of §3 ($\Xi \ne \emptyset$, sufficiently expensive recourse, $I\ge1$, $\hat\xi_i\in\Xi$, $\epsilon\ge0$). If problem (1) has complete recourse, then for every first-stage decision $x$
--   $$\mathcal Z(x) = \underline{\mathcal Z}(x) = \overline{\mathcal Z}(x):$$
--   the worst-case expectation, the completely positive program (14) and the copositive program (10) all have the same optimal value.
--
--   Hence under complete recourse problem (1) is equivalent to the copositive program obtained by replacing $\mathcal Z(x)$ with $\overline{\mathcal Z}(x)$. Without complete recourse the duality gap between (14) and (10) can be infinite (Example 1).
--
--   **Formalization Note** "For any fixed $x\in\mathcal X$" is stated for every $x \in \mathbb R^{N_1}$. Values are in `EReal`.
-- source:
--   Hanasusanto, Kuhn, Conic Programming Reformulations of Two-Stage Distributionally Robust Linear Programs over Wasserstein Balls, arXiv:1609.07505v3, p. 16, Theorem 4; proof pp. 16–17

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_ConicPrograms

namespace WassTwoStage.Copositive

/-- Theorem 4, Hanasusanto–Kuhn, arXiv:1609.07505v3, p. 16 (proof pp. 16–17): under the
standing assumptions of §3, if problem (1) has complete recourse then
`𝒵(x) = 𝒵̲(x) = 𝒵̄(x)` for every first-stage decision `x`: the worst-case expectation (2),
the completely positive program (14) and the copositive program (10) have the same value. -/
theorem theorem_4 {K J M N₁ N₂ I : ℕ} (d : Data K J M N₁ N₂ I) (hI : 0 < I)
    (hXi : d.Xi.Nonempty) (hSER : d.SufficientlyExpensiveRecourse)
    (hξ : ∀ i, d.ξhat i ∈ d.Xi) (hε : 0 ≤ d.ε) (hCR : d.CompleteRecourse)
    (x : Fin N₁ → ℝ) :
    d.worstCase x = d.lowerValue 0 x ∧ d.lowerValue 0 x = d.upperValue 0 x := by sorry

end WassTwoStage.Copositive
