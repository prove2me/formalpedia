-- Prove2me | Theorems.Thm_RobustMDP_Discounted_maxmin_value
-- name    : RobustMDP.Discounted.maxmin_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:00:45.758998+00:00
-- url     : https://prove2.me/theorems/e80f2f2b-5a39-40a7-99ea-bf55dbfaea4b
-- title:
--   Eqs. (27) and (19), pp. 785–786 — the max–min value $\psi_\infty(\Pi_s, \mathcal T_s)$ solves the robust Bellman equation
-- statement:
--   Fix an initial state $i_0$. The robust Bellman equation
--   $$v(i) = \min_{a \in \mathcal A} \big(c(i, a) + \nu\, \sigma_{\mathcal P_i^a}(v)\big), \qquad i \in \mathcal X, \tag{19}$$
--   has exactly one solution $v \in \mathbb R^n$, and the max–min value of the game between nature and the controller over stationary policies is
--   $$\psi_\infty(\Pi_s, \mathcal T_s) = \sup_{\tau \in \mathcal T_s} \min_{\pi \in \Pi_s} C_\infty(\pi, \tau) = v(i_0).$$
--
--   In the paper this value is the optimum of the nonlinear program (27), obtained from the linear program (25) of the nominal problem by letting nature's matrices become variables.
--
--   **Formalization Note** The minimum over the finite set $\Pi_s$ is `⨅`. The paper writes $\max_{\tau}$; the row sets need not be closed, so the outer supremum is stated as a least upper bound (`IsLUB`).
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 786, Eq. (27); p. 785, Theorem 3, Eq. (19)

import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_Discounted_discountedCost
import Definitions.Def_RobustMDP_Discounted_bellmanOps

namespace RobustMDP.Discounted

/-- Problem (27) and equation (19) (Nilim–El Ghaoui 2005, pp. 785–786). The equation (19)
`v(i) = min_{a ∈ 𝒜} (c(i, a) + ν σ_{𝒫_i^a}(v))`, `i ∈ 𝒳`, has exactly one solution `v ∈ ℝⁿ`,
and the max–min value `ψ_∞(Π_s, 𝒯_s) = sup_{P ∈ 𝒯_s} min_{π ∈ Π_s} C_∞(π, P)` from the initial
state `i₀` equals `v(i₀)`. The inner minimum over the finite set `Π_s` is `⨅`; the outer supremum
over the (generally infinite) set `𝒯_s` is stated as a least upper bound. -/
theorem maxmin_value {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A) (i₀ : Fin n) :
    ∃ v : Fin n → ℝ,
      M.bellmanOp v = v ∧ (∀ w, M.bellmanOp w = w → w = v) ∧
      IsLUB (Set.range fun P : M.StationaryNature =>
          ⨅ π : StationaryPolicy n A, M.discountedCost i₀ π P) (v i₀) := by sorry

end RobustMDP.Discounted
