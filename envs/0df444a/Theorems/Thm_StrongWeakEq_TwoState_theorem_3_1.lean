-- Prove2me | Theorems.Thm_StrongWeakEq_TwoState_theorem_3_1
-- name    : StrongWeakEq.TwoState.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:32:16.901442+00:00
-- url     : https://prove2.me/theorems/ea3df088-4e47-4f1b-b009-9785b456a3e5
-- title:
--   Theorem 3.1, p. 7 — under (2.3) and (3.3), Q* is a weak equilibrium iff Γ^{Q*}(Q*ᵢ) ≥ Γ^{Q*}(Qᵢ) for all (i, Q)
-- statement:
--   Let $S=\{1,\dots,N\}$, admissible rows $D_i\subseteq E_i$ and a payoff $f$ satisfy the standing assumptions (2.1)–(2.3) of §2, and suppose $f$ admits a shift bound $h$ as in (3.3)–(3.5). Let $Q^*\in\mathcal Q$. Then $Q^*$ is a weak equilibrium if and only if
--   $$
--   \Gamma^{Q^*}(Q^*_i)\ \ge\ \Gamma^{Q^*}(Q_i)\qquad\text{for all }(i,Q)\in S\times\mathcal Q, \tag{3.10}
--   $$
--   where $\Gamma^{Q^*}(q)=f(0,i,q)+q\cdot F(Q^*)$.
--
--   This first-order characterization reduces the search for weak equilibria to a family of static optimization problems, one per state; Example 4.3 uses it to show that $Q^*\sim(5/12,7/12)$ is a weak equilibrium.
--
--   **Formalization Note** The same statement is drafted in the companion mission on existence (sub-namespace `StrongWeakEq.Existence`); draft items cannot import each other, so it is restated here on this mission's copy of the model. Hypothesis (2.2), continuity of $f$ in $t$, is part of the standing assumptions `Standing` and is implied by (3.3) anyway.
-- source:
--   Huang & Zhou, Strong and Weak Equilibria for Time-Inconsistent Stochastic Control in Continuous Time, arXiv:1809.09243v3, p. 7, Theorem 3.1, (3.10)

import Mathlib
import Definitions.Def_StrongWeakEq_Existence_Model
import Definitions.Def_StrongWeakEq_Existence_SecondOrder

namespace StrongWeakEq.TwoState

/-- Theorem 3.1, p. 7: under the standing assumptions (2.1)–(2.3) and (3.3)–(3.5), `Q* ∈ 𝒬` is a
weak equilibrium if and only if `Γ^{Q*}(Q*ᵢ) ≥ Γ^{Q*}(Qᵢ)` for all `(i, Q) ∈ S × 𝒬` (3.10). -/
theorem theorem_3_1 {N : ℕ} (D : Fin N → Set (Fin N → ℝ))
    (f : ℝ → Fin N → (Fin N → ℝ) → ℝ) (hS : StrongWeakEq.Existence.Standing D f) (hSB : StrongWeakEq.Existence.ShiftBound D f)
    (Qs : Matrix (Fin N) (Fin N) ℝ) (hQs : Qs ∈ StrongWeakEq.Existence.Controls D) :
    StrongWeakEq.Existence.IsWeakEquilibrium D f Qs ↔
      ∀ i, ∀ Q ∈ StrongWeakEq.Existence.Controls D, StrongWeakEq.Existence.Gamma f Qs i (Q i) ≤ StrongWeakEq.Existence.Gamma f Qs i (Qs i) := by sorry

end StrongWeakEq.TwoState
