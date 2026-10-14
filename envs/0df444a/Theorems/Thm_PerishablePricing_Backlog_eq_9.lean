-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_eq_9
-- name    : PerishablePricing.Backlog.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:07.497679+00:00
-- url     : https://prove2.me/theorems/c0ea6bae-61ad-4b1c-a432-3c566e550fd5
-- title:
--   (9), p. 291 — φₜ is nonincreasing in a beyond s₍ₗ₋ₖ₎ ∨ dₜ, so gₜ = g̃ₜ
-- statement:
--   In the backlogging model with the standing assumptions of §3 and §4, fix a period $t \le T$, a feasible state $s \in \mathcal{S}$, an order-up-to level $s_l \ge s_{l-1}$, a demand level $d$ and a noise value $\varepsilon$, and write $d_t = d + \varepsilon$. For depletions $a' > a \ge s_{l-k} \vee d_t$, with $\delta = a' - a$ and next states $\tilde s$, $\tilde s'$,
--
--   $$\phi_t(s, s_l, d, a' \mid \varepsilon) - \phi_t(s, s_l, d, a \mid \varepsilon) = -(\gamma c + \theta + h^-)\delta + \gamma\big[f_{t+1}(\tilde s') - f_{t+1}(\tilde s)\big] \le -(\gamma c + \theta + h^-)\delta + \gamma(\theta + c)\delta \le 0.$$
--
--   Consequently the upper bound $a \le s_{l-k} \vee d_t$ in (5) can be dropped:
--
--   $$g_t(s, s_l, d \mid \varepsilon) = \tilde g_t(s, s_l, d \mid \varepsilon) = \sup_{a \ge s_1 \vee d_t} \phi_t(s, s_l, d, a \mid \varepsilon).$$
--
--   **Formalization Note** The page prints "$< 0$" at the end of (9). The bound equals $-(1 - \gamma)\theta\delta - h^-\delta$, which is $0$ when $h^- = 0$ and either $\gamma = 1$ or $\theta = 0$, so the strict inequality is replaced by $\le 0$; this is all the conclusion $g_t = \tilde g_t$ needs, and no hypothesis $h^- > 0$ is added. The page writes $\phi_t(s, s_l, a, d)$ with $a$ before $d$; the argument order of (6) is used. $d$ and $\varepsilon$ are arbitrary reals, as on the page. Time is counted in periods to go: the continuation of `phiN n` is `f n`. The §4 assumption $c \le h^-/(1-\gamma)$ is the hypothesis $(1 - \gamma)c \le h^-$.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, eq. (9) and the definition of g̃_t, p. 291 (PDF p. 9)

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Model

namespace PerishablePricing.Backlog

/-- (9), p. 291: with `n + 1` periods to go, a feasible state `s`, `s_l ≥ s_{l−1}`, any `d`, `ε`,
and depletions `a′ > a ≥ s_{l−k} ∨ d_t` (`d_t = d + ε`, `δ = a′ − a`),
`φ_t(a′) − φ_t(a) = −(γc + θ + h⁻)δ + γ[f_{t+1}(s̃′) − f_{t+1}(s̃)] ≤ −(γc + θ + h⁻)δ + γ(θ + c)δ ≤ 0`,
and hence `g_t(s, s_l, d | ε) = g̃_t(s, s_l, d | ε)`. The page's strict `< 0` is weakened to `≤ 0`
(the bound equals `−(1 − γ)θδ − h⁻δ`, which is `0` when `h⁻ = 0` and `γ = 1` or `θ = 0`). -/
theorem eq_9 {L k : ℕ} (M : Model L k) (hc : (1 - M.γ) * M.c ≤ M.hm) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ Model.StateSpace L) (sl : ℝ) (hsl : M.sLast s ≤ sl) (d ε : ℝ) :
    (∀ a a' : ℝ, max (M.netInv s sl) (d + ε) ≤ a → a < a' →
      M.phiN n s sl d a' ε - M.phiN n s sl d a ε
          = -(M.γ * M.c + M.θ + M.hm) * (a' - a)
            + M.γ * (M.f n (Model.next s sl a') - M.f n (Model.next s sl a)) ∧
        M.phiN n s sl d a' ε - M.phiN n s sl d a ε
          ≤ -(M.γ * M.c + M.θ + M.hm) * (a' - a) + M.γ * (M.θ + M.c) * (a' - a) ∧
        -(M.γ * M.c + M.θ + M.hm) * (a' - a) + M.γ * (M.θ + M.c) * (a' - a) ≤ 0) ∧
      M.gN n s sl d ε = M.gtildeN n s sl d ε := by sorry

end PerishablePricing.Backlog
