-- Prove2me | Theorems.Thm_PerishablePricing_Bounds_phi_min_disposal_decomposition
-- name    : PerishablePricing.Bounds.phi_min_disposal_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:17:00.233871+00:00
-- url     : https://prove2.me/theorems/1ec594ae-ee10-41fd-b8e4-7128cca36b81
-- title:
--   §6.1, p. 294 — at a = d_t ∨ s₁, φ_t = v_t(s_l, d_t) − θ̃(s₁ − d_t)⁺ + γ f_{t+1}(s̃)
-- statement:
--   Consider the backlogging model with lifetime $l\ge 2$ and zero lead time, under the standing assumptions of §3, §4 and §6.1 ($\gamma<1$, $\theta\ge h^+/(1-\gamma)$). For every state $s\in\mathcal S$, every order-up-to level $s_l\ge s_{l-1}$, every $d$ and every noise value $\varepsilon$, with $d_t=d+\varepsilon$ and the minimal depletion $a=d_t\vee s_1$,
--
--   $$\varphi_t(s,s_l,d,\ d_t\vee s_1\mid\varepsilon)=v_t(s_l,d_t)-\tilde\theta\,(s_1-d_t)^++\gamma f_{t+1}(\tilde s),$$
--
--   where $v_t(s_l,d_t)=-(1-\gamma)cs_l-\gamma cd_t-h^+(s_l-d_t)^+-h^-(d_t-s_l)^+$, $\tilde\theta=\theta+\gamma c-h^+$ and $\tilde s=(s_2-a,\dots,s_l-a)$.
--
--   The decomposition separates the part of the period's profit that depends on the order-up-to level ($v_t$ and the continuation) from the disposal of expiring stock.
--
--   **Formalization Note.** Time is counted in periods to go: $f_{t+1}$ is `f n`. The identity uses only $s_1\le s_l$, which follows from $s\in\mathcal S$ and $s_l\ge s_{l-1}$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, §6.1, p. 294, display after 'When a_t = d_t ∨ s_1, we have'

import Mathlib
import Definitions.Def_PerishablePricing_Bounds_Myopic

namespace PerishablePricing.Bounds

/-- §6.1, p. 294, the display after "When `a_t = d_t ∨ s₁`, we have" (zero lead time, backlogging):
at the minimal depletion `a = d_t ∨ s₁`,
`φ_t(s, s_l, d, d_t ∨ s₁ | ε) = v_t(s_l, d_t) − θ̃ (s₁ − d_t)⁺ + γ f_{t+1}(s̃)`,
with `d_t = d + ε`, `θ̃ = θ + γc − h⁺` and `s̃ = (s₂ − a, …, s_l − a)`, for every state `s ∈ 𝒮`
and order-up-to level `s_l ≥ s_{l−1}`. -/
theorem phi_min_disposal_decomposition (M : Model) (hM : M.Standing) (L : ℕ) (hL : 1 ≤ L)
    (hback : (1 - M.γ) * M.c ≤ M.hm) (hγ : M.γ < 1) (hθ : M.hp ≤ (1 - M.γ) * M.θ) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ stateSpace L) (sl : ℝ) (hsl : sLast s ≤ sl) (d ε : ℝ) :
    M.phi (M.f n) s sl d (max (d + ε) (sFirst s)) ε =
      M.v sl (d + ε) - M.θt * max (sFirst s - (d + ε)) 0
        + M.γ * M.f n (next s sl (max (d + ε) (sFirst s))) := by sorry

end PerishablePricing.Bounds
