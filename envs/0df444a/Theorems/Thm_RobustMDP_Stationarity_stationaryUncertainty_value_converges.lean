-- Prove2me | Theorems.Thm_RobustMDP_Stationarity_stationaryUncertainty_value_converges
-- name    : RobustMDP.Stationarity.stationaryUncertainty_value_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:25:26.333087+00:00
-- url     : https://prove2.me/theorems/82fee87c-44b6-4cb4-83eb-2a5b6b8e0c9a
-- title:
--   Step (e), p. 787 — $\phi_N(\Pi,\mathcal T_s)\to\phi_\infty(\Pi,\mathcal T_s)$ at geometric rate $\nu$
-- statement:
--   In a robust discounted MDP with discount factor $0<\nu<1$ (finite states, finite nonempty action set, costs $c\ge0$, nonempty rectangular row sets in the simplex), for every horizon $N$
--   $$
--   \phi_N(\Pi,\mathcal T_s)\le\phi_\infty(\Pi,\mathcal T_s)\le\phi_N(\Pi,\mathcal T_s)+\varepsilon_N,\qquad \varepsilon_N=\frac{\nu^N c_{\max}}{1-\nu},
--   $$
--   where $\phi_N(\Pi,\mathcal T_s)=\inf_{\pi\in\Pi}\sup_{\tau\in\mathcal T_s}C_N(\pi,\tau)$ is the robust value when nature must use the same transition matrices at every stage, and $\phi_\infty(\Pi,\mathcal T_s)$ its infinite-horizon counterpart.
--
--   Together with Eq. (35) this bounds the gap between time-varying and stationary uncertainty in Theorem 4.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 787, proof of Theorem 4, Step (e), first display

import Mathlib
import Definitions.Def_RobustMDP_Stationarity_Model
import Definitions.Def_RobustMDP_Stationarity_gameValues

namespace RobustMDP.Stationarity

/-- Nilim–El Ghaoui 2005, p. 787, Step (e): for every `N`,
`φ_N(Π, 𝒯_s) ≤ φ_∞(Π, 𝒯_s) ≤ φ_N(Π, 𝒯_s) + ε_N`. -/
theorem stationaryUncertainty_value_converges {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n) (N : ℕ) :
    M.phiN_PTs ν i₀ N ≤ M.phiInf_PTs ν i₀ ∧
      M.phiInf_PTs ν i₀ ≤ M.phiN_PTs ν i₀ N + M.epsN ν N := by sorry

end RobustMDP.Stationarity
