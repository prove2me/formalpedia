-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_proposition_1
-- name    : PerishablePricing.Backlog.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:27.417876+00:00
-- url     : https://prove2.me/theorems/0ff8d102-2dbc-4d41-963b-35cf97dd32ee
-- title:
--   Proposition 1, p. 292 — if θ ≥ h⁺/(1 − γ), depleting dₜ ∨ s₁ is optimal
-- statement:
--   In the backlogging model with the standing assumptions of §3 and §4, suppose $\gamma < 1$ and
--
--   $$\theta \ge \frac{h^+}{1 - \gamma}.$$
--
--   Then in every period, for every feasible state $s$, order-up-to level $s_l \ge s_{l-1}$, demand level $d \in \mathcal{D}$ and noise value $\varepsilon$ in the support $[A, B]$, the minimum depletion
--
--   $$a = d_t \vee s_1, \qquad d_t = d + \varepsilon,$$
--
--   is optimal in (5): it is feasible and attains $g_t(s, s_l, d \mid \varepsilon)$. When disposal costs more than holding a unit forever, inventory is disposed of only when it expires.
--
--   **Formalization Note** The quotient $h^+/(1-\gamma)$ requires $\gamma < 1$, which is made explicit, and the condition is written $h^+ \le (1-\gamma)\theta$. The page says "the optimal depletion decision is always equal to $d_t \vee s_1$"; ties can occur (for instance at $\theta = h^+/(1-\gamma)$), so the statement asserts that $d_t \vee s_1$ is an optimal depletion, not that it is the unique one. The realized demand ranges over its possible values, $d \in \mathcal{D}$ and $\varepsilon \in [A, B]$. The §4 assumption is the hypothesis $(1 - \gamma)c \le h^-$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, Proposition 1, p. 292 (PDF p. 10)

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Model

namespace PerishablePricing.Backlog

/-- Proposition 1 (Minimum Disposal), p. 292. Suppose `θ ≥ h⁺/(1 − γ)` (with `γ < 1`, written
`h⁺ ≤ (1 − γ)θ`). Then for every number of periods to go, every feasible state `s`, order-up-to
level `s_l ≥ s_{l−1}`, demand level `d ∈ 𝒟` and noise value `ε ∈ [A, B]`, the depletion
`d_t ∨ s_1` (`d_t = d + ε`) is optimal in (5). -/
theorem proposition_1 {L k : ℕ} (M : Model L k) (hc : (1 - M.γ) * M.c ≤ M.hm)
    (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ Model.StateSpace L) (sl : ℝ) (hsl : M.sLast s ≤ sl)
    (d : ℝ) (hd : d ∈ Set.Icc M.dlo M.dhi) (ε : ℝ) (hε : ε ∈ Set.Icc M.A M.B) :
    M.IsOptDepletion n s sl d ε (max (d + ε) (M.s1 s)) := by sorry

end PerishablePricing.Backlog
