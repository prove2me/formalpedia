-- Prove2me | Theorems.Thm_RobustMDP_Stationarity_stationaryNature_policy_stationary
-- name    : RobustMDP.Stationarity.stationaryNature_policy_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:27:42.542257+00:00
-- url     : https://prove2.me/theorems/4e212063-dcc6-4e8a-93c9-950d7b878746
-- title:
--   Step (d), p. 787 — $\phi_\infty(\Pi,\mathcal T_s)=\phi_\infty(\Pi_s,\mathcal T_s)$
-- statement:
--   In a robust discounted MDP with discount factor $0<\nu<1$ (finite states, finite nonempty action set, costs $c\ge0$, nonempty rectangular row sets in the simplex), when nature is restricted to stationary policies, allowing the controller time-varying policies does not lower the robust value:
--   $$
--   \phi_\infty(\Pi,\mathcal T_s)=\phi_\infty(\Pi_s,\mathcal T_s).
--   $$
--
--   This is Step (d) of the proof of Theorem 4, the last equality of (31).
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 787, proof of Theorem 4, Step (d), first display

import Mathlib
import Definitions.Def_RobustMDP_Stationarity_Model
import Definitions.Def_RobustMDP_Stationarity_gameValues

namespace RobustMDP.Stationarity

/-- Nilim–El Ghaoui 2005, p. 787, Step (d): `φ_∞(Π, 𝒯_s) = φ_∞(Π_s, 𝒯_s)`. -/
theorem stationaryNature_policy_stationary {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n) :
    M.phiInf_PTs ν i₀ = M.phiInf_PsTs ν i₀ := by sorry

end RobustMDP.Stationarity
