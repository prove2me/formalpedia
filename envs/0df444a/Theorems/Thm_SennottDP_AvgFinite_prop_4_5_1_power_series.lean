-- Prove2me | Theorems.Thm_SennottDP_AvgFinite_prop_4_5_1_power_series
-- name    : SennottDP.AvgFinite.prop_4_5_1_power_series
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T08:17:40.963846+00:00
-- url     : https://prove2.me/theorems/1207829d-8ed9-4f3d-824a-1f78604354b2
-- title:
--   Proposition 4.5.1 — V_{θ,α}(i) is a power series in α with a radius of convergence, smooth inside it
-- statement:
--   Let $\Delta$ be an MDC with countable state space, $\theta$ a policy and $i$ an initial state. Put $u_n = E_\theta[C(X_n,A_n) \mid X_0 = i] \in [0,\infty]$, so that
--   $$V_{\theta,\alpha}(i) = \sum_{n=0}^{\infty} \alpha^n u_n, \qquad \alpha \in [0,\infty). \tag{4.24}$$
--   Then there is a radius of convergence $R_i \in [0,\infty]$: the series is finite for $0 \le \alpha < R_i$ and infinite for $\alpha > R_i$. If $R_i > 0$, then $\alpha \mapsto V_{\theta,\alpha}(i)$ is infinitely differentiable (and hence continuous) on $(0,R_i)$.
--
--   This places the discounted cost of a fixed policy in the setting of power series in the discount factor, the viewpoint used in Chapter 6 to pass from discounted to average cost.
--
--   **Formalization Note** $R_i$ is in `ℝ≥0∞` and is characterized by finiteness of the series below it and divergence above it. Smoothness is `ContDiffOn ℝ ⊤` of `α ↦ (V_{θ,α}(i)).toReal` on $\{\alpha : 0 < \alpha < R_i\}$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 70, Proposition 4.5.1, Eq. (4.24)

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Criteria

namespace SennottDP.AvgFinite

open scoped ENNReal NNReal

/-- Proposition 4.5.1 (Sennott, p. 70). For a policy `θ` and an initial state `i`, the power series
(4.24) `V_{θ,α}(i) = ∑_n α^n u_n`, `u_n = E_θ[C(X_n,A_n) | X_0 = i]`, `α ∈ [0,∞)`, has a radius of
convergence `R_i ∈ [0,∞]` (it converges for `0 ≤ α < R_i` and diverges for `α > R_i`), and if
`R_i > 0` then `α ↦ V_{θ,α}(i)` is infinitely differentiable on `(0, R_i)`. -/
theorem prop_4_5_1_power_series {S : Type*} {Act : Type*} [Countable S] (M : MDC S Act)
    (θ : Policy M) (i : S) :
    ∃ R : ℝ≥0∞,
      (∀ α : ℝ, 0 ≤ α → ENNReal.ofReal α < R → discCost θ α i ≠ ⊤) ∧
      (∀ α : ℝ, R < ENNReal.ofReal α → discCost θ α i = ⊤) ∧
      (0 < R → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun α : ℝ => (discCost θ α i).toReal)
        {α : ℝ | 0 < α ∧ ENNReal.ofReal α < R}) := by sorry

end SennottDP.AvgFinite
