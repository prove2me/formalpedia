-- Prove2me | Theorems.Thm_RobustMDP_Stationarity_stationaryPolicy_nature_stationary
-- name    : RobustMDP.Stationarity.stationaryPolicy_nature_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:26:29.177865+00:00
-- url     : https://prove2.me/theorems/09599aca-5fe8-47e1-9347-aa5b1e28b939
-- title:
--   Step (c), p. 787 — against a stationary controller, stationary nature is as bad as time-varying nature
-- statement:
--   In a robust discounted MDP with discount factor $0<\nu<1$ (finite states, finite nonempty action set, costs $c\ge0$, nonempty rectangular row sets in the simplex), for every stationary controller policy $\pi\in\Pi_s$,
--   $$
--   \phi_\infty(\pi,\mathcal T):=\sup_{\tau\in\mathcal T}C_\infty(\pi,\tau)=\sup_{\tau\in\mathcal T_s}C_\infty(\pi,\tau)=:\phi_\infty(\pi,\mathcal T_s),
--   $$
--   and consequently $\phi_\infty(\Pi_s,\mathcal T)=\phi_\infty(\Pi_s,\mathcal T_s)$.
--
--   This is Step (c) of the proof of Theorem 4, the second equality of (31).
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 787, proof of Theorem 4, Step (c)

import Mathlib
import Definitions.Def_RobustMDP_Stationarity_Model
import Definitions.Def_RobustMDP_Stationarity_gameValues

namespace RobustMDP.Stationarity

/-- Nilim–El Ghaoui 2005, p. 787, Step (c): for every stationary controller policy `π ∈ Π_s`,
the worst case over time-varying nature equals the worst case over stationary nature,
`φ_∞(π, 𝒯) = φ_∞(π, 𝒯_s)`; hence `φ_∞(Π_s, 𝒯) = φ_∞(Π_s, 𝒯_s)`. -/
theorem stationaryPolicy_nature_stationary {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n) :
    (∀ π : Fin n → A,
      (⨆ τ : M.NaturePolicy, M.infCost ν i₀ (fun _ => π) τ) =
        ⨆ P : M.Choice, M.infCost ν i₀ (fun _ => π) (fun _ => P)) ∧
      M.phiInf_PsT ν i₀ = M.phiInf_PsTs ν i₀ := by sorry

end RobustMDP.Stationarity
