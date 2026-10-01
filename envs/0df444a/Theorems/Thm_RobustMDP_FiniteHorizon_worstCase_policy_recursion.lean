-- Prove2me | Theorems.Thm_RobustMDP_FiniteHorizon_worstCase_policy_recursion
-- name    : RobustMDP.FiniteHorizon.worstCase_policy_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:21:10.03726+00:00
-- url     : https://prove2.me/theorems/f84e3753-68cc-4512-b79f-19cdedbd4b8f
-- title:
--   Eq. (16), p. 783 — the worst-case cost of a fixed policy is given by recursion (10)
-- statement:
--   Consider a finite-horizon robust MDP with nonempty row sets $\mathcal P_i^a\subseteq\Delta_n$, an initial state $i_0$ and a controller policy $\pi$. The worst-case expected total cost of $\pi$ over all admissible policies of nature,
--
--   $$
--   \varphi_N(\pi,\mathcal T)=\sup_{\tau\in\mathcal T}C_N(\pi,\tau),
--   $$
--
--   equals $v_0^\pi(i_0)$, where $v^\pi$ is computed by recursion (10): $v_N^\pi=c_N$ and $v_t^\pi(i)=c_t(i,\mathbf a_t(i))+\sigma_{\mathcal P_i^{\mathbf a_t(i)}}(v_{t+1}^\pi)$.
--
--   This is the paper's problem (16) solved by Lemma 1: the rectangular structure of $\mathcal T$ lets nature optimise each row separately, which is where the support functions come from.
--
--   **Formalization Note** The paper writes "max"; since the sets $\mathcal P_i^a$ need not be closed, the worst case is a supremum, stated as a least upper bound (`IsLUB`) of the set of costs $\{C_N(\pi,\tau):\tau\in\mathcal T\}$.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 783, Eq. (16) and the paragraph after it; Theorem 1, Eq. (10)

import Mathlib
import Definitions.Def_RobustMDP_Shared_supportFunction
import Definitions.Def_RobustMDP_FiniteHorizon_Model
import Definitions.Def_RobustMDP_FiniteHorizon_expectedCost
import Definitions.Def_RobustMDP_FiniteHorizon_robustValue

namespace RobustMDP.FiniteHorizon

/-- Problem (16), p. 783, solved by recursion (10). For every controller policy `π`, the
worst-case expected total cost `φ_N(π, 𝒯) = sup_{τ ∈ 𝒯} C_N(π, τ)` over all admissible
(time-varying, rectangular) policies of nature is the value `v_0^π(i₀)` of the recursion
`v_t^π(i) = c_t(i, 𝐚_t(i)) + σ_{𝒫_i^{𝐚_t(i)}}(v_{t+1}^π)`, `v_N^π = c_N`. The paper's "max"
is stated as a least upper bound, since the row sets need not be closed. -/
theorem worstCase_policy_recursion {n N : ℕ} {A : Type} (M : Model n N A) (i₀ : Fin n)
    (π : ControlPolicy n N A) :
    IsLUB (Set.range fun τ : M.NaturePolicy => M.expectedCost i₀ π τ.1)
      (M.policyValue π 0 i₀) := by sorry

end RobustMDP.FiniteHorizon
