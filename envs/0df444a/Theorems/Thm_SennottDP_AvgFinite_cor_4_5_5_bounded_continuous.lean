-- Prove2me | Theorems.Thm_SennottDP_AvgFinite_cor_4_5_5_bounded_continuous
-- name    : SennottDP.AvgFinite.cor_4_5_5_bounded_continuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T08:35:23.350779+00:00
-- url     : https://prove2.me/theorems/4477e26a-e96a-4c3b-8915-b11a214e658c
-- title:
--   Corollary 4.5.5 — with bounded costs, V_α is finite and continuous on (0,1)
-- statement:
--   Let $\Delta$ be an MDC with countable state space. If there is a finite constant $B$ such that $C(i,a) \le B$ for all states $i$ and actions $a \in A_i$, then for every state $i$ the discounted value function $V_\alpha(i)$ is finite and continuous in $\alpha \in (0,1)$.
--
--   With bounded costs this upgrades the left continuity of Proposition 4.5.4 to continuity.
--
--   **Formalization Note** Finiteness is `V_α(i) ≠ ⊤` for $\alpha \in (0,1)$; continuity is stated for the real value `toReal` on $(0,1)$. $B$ ranges over `ℝ≥0`.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 73, Corollary 4.5.5

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Criteria

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal

/-- Corollary 4.5.5 (Sennott, p. 73). If there is a finite constant `B` with `C(i,a) ≤ B` for all
state-action pairs, then `V_α` is finite and continuous for `α ∈ (0,1)`. -/
theorem cor_4_5_5_bounded_continuous {S : Type*} {Act : Type*} [Countable S] (M : MDC S Act)
    (hB : ∃ B : ℝ≥0, ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B) (i : S) :
    (∀ α ∈ Set.Ioo (0 : ℝ) 1, discValue M α i ≠ ⊤) ∧
    ContinuousOn (fun α : ℝ => (discValue M α i).toReal) (Set.Ioo 0 1) := by sorry

end SennottDP.AvgFinite
