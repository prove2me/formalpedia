-- Prove2me | Theorems.Thm_RobustMDP_Stationarity_timeVarying_value_converges
-- name    : RobustMDP.Stationarity.timeVarying_value_converges
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:24:48.171973+00:00
-- url     : https://prove2.me/theorems/f70e06e3-4c97-4e81-b536-0b874058a7ff
-- title:
--   Eq. (35), p. 786 — $\phi_N(\Pi,\mathcal T)\to\phi_\infty(\Pi,\mathcal T)$ at geometric rate $\nu$
-- statement:
--   In a robust discounted MDP with discount factor $0<\nu<1$ (finite states, finite nonempty action set, costs $c\ge0$, nonempty rectangular row sets in the simplex), for every horizon $N$
--   $$
--   \phi_N(\Pi,\mathcal T)\le\phi_\infty(\Pi,\mathcal T)\le\phi_N(\Pi,\mathcal T)+\varepsilon_N,\qquad \varepsilon_N=\frac{\nu^N c_{\max}}{1-\nu},
--   $$
--   where $\phi_N(\Pi,\mathcal T)=\inf_{\pi\in\Pi}\sup_{\tau\in\mathcal T}C_N(\pi,\tau)$ is the finite-horizon robust value under time-varying uncertainty and $\phi_\infty(\Pi,\mathcal T)$ its infinite-horizon counterpart.
--
--   Hence the finite-horizon robust values converge to the infinite-horizon one geometrically at rate $\nu$ (Step (b) of the proof of Theorem 4).
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 786, Eq. (35) (proof of Theorem 4, Step (b))

import Mathlib
import Definitions.Def_RobustMDP_Stationarity_Model
import Definitions.Def_RobustMDP_Stationarity_gameValues

namespace RobustMDP.Stationarity

/-- Nilim–El Ghaoui 2005, p. 786, Step (b), Eq. (35): for every `N`,
`φ_N(Π, 𝒯) ≤ φ_∞(Π, 𝒯) ≤ φ_N(Π, 𝒯) + ε_N`. -/
theorem timeVarying_value_converges {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A)
    (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n) (N : ℕ) :
    M.phiN_PT ν i₀ N ≤ M.phiInf_PT ν i₀ ∧
      M.phiInf_PT ν i₀ ≤ M.phiN_PT ν i₀ N + M.epsN ν N := by sorry

end RobustMDP.Stationarity
