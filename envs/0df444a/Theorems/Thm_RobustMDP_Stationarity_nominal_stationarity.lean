-- Prove2me | Theorems.Thm_RobustMDP_Stationarity_nominal_stationarity
-- name    : RobustMDP.Stationarity.nominal_stationarity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:27:01.687039+00:00
-- url     : https://prove2.me/theorems/672501df-45b1-436f-90c8-ef218056fa30
-- title:
--   Step (d), p. 787 — nominal stationarity (Puterman 1994): $\phi_N(\Pi,\tau)\to\phi_\infty(\Pi_s,\tau)$ for stationary $\tau$
-- statement:
--   Fix a robust discounted MDP with discount factor $0<\nu<1$ (finite states, finite nonempty action set, costs $c\ge0$, nonempty rectangular row sets in the simplex) and a stationary nature policy $\tau\in\mathcal T_s$, that is, fixed transition matrices $(P^a)_{a}$ with rows $P^a(i,\cdot)\in\mathcal P_i^a$ used at every stage. Then the nominal finite-horizon optimal values converge to the nominal infinite-horizon optimal value over stationary policies:
--   $$
--   \phi_N(\Pi,\tau):=\inf_{\pi\in\Pi}C_N(\pi,\tau)\ \xrightarrow[N\to\infty]{}\ \phi_\infty(\Pi_s,\tau):=\inf_{\pi\in\Pi_s}C_\infty(\pi,\tau).
--   $$
--
--   The paper imports this from the classical theory of discounted MDPs (Puterman 1994) and uses it in Step (d) of the proof of Theorem 4.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 787, proof of Theorem 4, Step (d), citing Puterman (1994)

import Mathlib
import Definitions.Def_RobustMDP_Stationarity_Model

namespace RobustMDP.Stationarity

/-- Nilim–El Ghaoui 2005, p. 787, Step (d), the nominal fact cited to Puterman (1994): for every
stationary nature policy `τ = (P, P, …) ∈ 𝒯_s`, `φ_N(Π, τ) = inf_{π ∈ Π} C_N(π, τ)` converges,
as `N → ∞`, to `φ_∞(Π_s, τ) = inf_{π ∈ Π_s} C_∞(π, τ)`. -/
theorem nominal_stationarity {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n) (P : M.Choice) :
    Filter.Tendsto (fun N : ℕ => ⨅ π : Policy n A, M.finiteCost ν i₀ N π (fun _ => P))
      Filter.atTop
      (nhds (⨅ π : Fin n → A, M.infCost ν i₀ (fun _ => π) (fun _ => P))) := by sorry

end RobustMDP.Stationarity
