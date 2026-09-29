-- Prove2me | Theorems.Thm_RobustMDP_Discounted_worstCase_policy_eval
-- name    : RobustMDP.Discounted.worstCase_policy_eval
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:59:42.175558+00:00
-- url     : https://prove2.me/theorems/de1d81aa-f218-4de6-beb8-72f504a1981a
-- title:
--   Eqs. (28) and (23), pp. 785–786 — the worst-case cost of a stationary policy solves the robust evaluation equation
-- statement:
--   Fix an initial state $i_0$ and a stationary control policy $\pi = (\mathbf a, \mathbf a, \dots)$. The equation
--   $$v^\pi(i) = c(i, \mathbf a(i)) + \nu\, \sigma_{\mathcal P_i^{\mathbf a(i)}}(v^\pi), \qquad i \in \mathcal X, \tag{23}$$
--   has exactly one solution $v^\pi \in \mathbb R^n$, and the worst-case discounted cost of $\pi$ over stationary policies of nature is
--   $$\phi_\infty(\pi, \mathcal T_s) = \sup_{\tau \in \mathcal T_s} C_\infty(\pi, \tau) = v^\pi(i_0).$$
--
--   In the paper this value is the optimum of the nonlinear program (28), obtained from (26) by letting nature's matrices become variables; (23) is its characterization.
--
--   **Formalization Note** The paper writes $\max_{\tau \in \mathcal T_s}$. The row sets need not be closed, so the supremum need not be attained, and it is stated as a least upper bound (`IsLUB`) of the set of costs $C_\infty(\pi, \tau)$, $\tau \in \mathcal T_s$.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 786, Eq. (28); p. 785, Theorem 3, Eq. (23)

import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_Discounted_discountedCost
import Definitions.Def_RobustMDP_Discounted_bellmanOps

namespace RobustMDP.Discounted

/-- Problem (28) and equation (23) (Nilim–El Ghaoui 2005, pp. 785–786). For every stationary
controller policy `π = (𝐚, 𝐚, …)`, the equation (23)
`v^π(i) = c(i, 𝐚(i)) + ν σ_{𝒫_i^{𝐚(i)}}(v^π)`, `i ∈ 𝒳`, has exactly one solution `v^π ∈ ℝⁿ`,
and the worst-case discounted cost `φ_∞(π, 𝒯_s) = sup_{P ∈ 𝒯_s} C_∞(π, P)` from the initial
state `i₀` equals `v^π(i₀)`. The supremum over the (generally infinite) set `𝒯_s` is stated as a
least upper bound, since it need not be attained. -/
theorem worstCase_policy_eval {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n)
    (π : StationaryPolicy n A) :
    ∃ vπ : Fin n → ℝ,
      M.policyOp π vπ = vπ ∧ (∀ w, M.policyOp π w = w → w = vπ) ∧
      IsLUB (Set.range fun P : M.StationaryNature => M.discountedCost i₀ π P) (vπ i₀) := by sorry

end RobustMDP.Discounted
