-- Prove2me | Theorems.Thm_RobustMDP_FiniteHorizon_maxmin_recursion
-- name    : RobustMDP.FiniteHorizon.maxmin_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:21:53.661647+00:00
-- url     : https://prove2.me/theorems/9b1c32fe-802f-433c-bc29-5590ada95cf5
-- title:
--   Eq. (15), p. 783 — the max–min value $\psi_N(\Pi,\mathcal T)$ is given by recursion (7)
-- statement:
--   Consider a finite-horizon robust MDP with nonempty row sets $\mathcal P_i^a\subseteq\Delta_n$ and an initial state $i_0$. The max–min value, in which nature commits to $\tau\in\mathcal T$ and the controller then chooses a policy,
--
--   $$
--   \psi_N(\Pi,\mathcal T)=\sup_{\tau\in\mathcal T}\ \min_{\pi\in\Pi}C_N(\pi,\tau),
--   $$
--
--   equals $v_0(i_0)$, where $v$ is computed by the robust recursion (7): $v_N=c_N$ and $v_t(i)=\min_{a\in\mathcal A}\big(c_t(i,a)+\sigma_{\mathcal P_i^a}(v_{t+1})\big)$.
--
--   This is the paper's problem (15), a nonlinear program in the value functions and the transition matrices, solved by Lemma 1 thanks to rectangularity. Together with weak duality and recursion (10) it gives the perfect duality of Theorem 1.
--
--   **Formalization Note** $\Pi$ is finite and nonempty, so the inner minimum is Lean's `⨅ π`. The paper's "max" over nature is a supremum, since the row sets need not be closed; it is stated as a least upper bound (`IsLUB`).
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 783, Eq. (15) and the paragraph after (16); Theorem 1, Eq. (7)

import Mathlib
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_FiniteHorizon_Model
import Definitions.Def_RobustMDP_FiniteHorizon_expectedCost
import Definitions.Def_RobustMDP_FiniteHorizon_robustValue

namespace RobustMDP.FiniteHorizon

/-- Problem (15), p. 783, solved by recursion (7). The max–min value
`ψ_N(Π, 𝒯) = sup_{τ ∈ 𝒯} min_{π ∈ Π} C_N(π, τ)` (nature moves first, the controller responds
with a deterministic Markov policy) equals the value `v_0(i₀)` of the robust recursion
`v_t(i) = min_{a ∈ 𝒜} (c_t(i, a) + σ_{𝒫_i^a}(v_{t+1}))`, `v_N = c_N`. The minimum over the
finite nonempty set `Π` is `⨅ π`; the paper's "max" over nature is stated as a least upper
bound, since the row sets need not be closed. -/
theorem maxmin_recursion {n N : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n N A) (i₀ : Fin n) :
    IsLUB (Set.range fun τ : M.NaturePolicy => ⨅ π : ControlPolicy n N A, M.expectedCost i₀ π τ.1)
      (M.robustValue 0 i₀) := by sorry

end RobustMDP.FiniteHorizon
