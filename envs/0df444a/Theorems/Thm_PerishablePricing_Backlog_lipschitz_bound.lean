-- Prove2me | Theorems.Thm_PerishablePricing_Backlog_lipschitz_bound
-- name    : PerishablePricing.Backlog.lipschitz_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:26:15.77518+00:00
-- url     : https://prove2.me/theorems/c92aaff8-2efc-41c6-b9f5-7049fb06f62e
-- title:
--   p. 291 — δ more units of backorders change the profit-to-go by at most (θ + c)δ
-- statement:
--   In the backlogging model with the standing assumptions of §3 and §4, take a feasible state $s$, order-up-to level $s_l \ge s_{l-1}$, demand realization $d_t=d+\varepsilon$, and two depletion levels $a' > a \ge s_{l-k} \vee d_t$. Put $\delta=a'-a$, $\tilde s=(s_2-a,\ldots,s_l-a)$, and $\tilde s'=(s_2-a',\ldots,s_l-a')$. Then
--
--   $$f_{t+1}(\tilde s') - f_{t+1}(\tilde s) \le (\theta + c)\,\delta.$$
--
--   The two next states have the same on-order profile, while $\tilde s'$ has $\delta$ more units of backorders. This is the estimate used in (9) beyond $s_{l-k} \vee d_t$.
--
--   **Formalization Note** Time is counted in periods to go: `f n` is $f_{t+1}$ here, with $n=T-t$. The standing assumption of §4, $c \le h^-/(1 - \gamma)$, is the hypothesis $(1 - \gamma)c \le h^-$, the faithful reading also at $\gamma = 1$. The Lean quantifies over the two states constructed in the cited argument.
-- source:
--   Chen, Pang, Pan, Coordinating Inventory Control and Pricing Strategies for Perishable Products, Oper. Res. 62(2), 2014, §4, proof of Theorem 1, p. 291 (PDF p. 9), display after "Because of the suboptimality of the constructed policy, we have"

import Mathlib
import Definitions.Def_PerishablePricing_Backlog_Model

namespace PerishablePricing.Backlog

/-- p. 291, proof of Theorem 1, display after "Because of the suboptimality of the constructed
policy": for `a′ > a ≥ s_{l−k} ∨ d_t`, the resulting next states are `s̃ = next s sl a` and
`s̃′ = next s sl a′ = s̃ − (a′ − a)e`. The modified profit-to-go obeys
`f_{t+1}(s̃′) − f_{t+1}(s̃) ≤ (θ + c)(a′ − a)`. The standing assumption of §4,
`c ≤ h⁻/(1 − γ)`, is stated as `(1 − γ)c ≤ h⁻`. -/
theorem lipschitz_bound {L k : ℕ} (M : Model L k) (hc : (1 - M.γ) * M.c ≤ M.hm) (n : ℕ)
    (s : Fin L → ℝ) (hs : s ∈ Model.StateSpace L)
    (sl : ℝ) (hsl : M.sLast s ≤ sl) (d ε a a' : ℝ)
    (ha : max (M.netInv s sl) (d + ε) ≤ a) (haa' : a < a') :
    M.f n (Model.next s sl a') - M.f n (Model.next s sl a) ≤
      (M.θ + M.c) * (a' - a) := by sorry

end PerishablePricing.Backlog
