-- Prove2me | Theorems.Thm_RobustMDP_Stationarity_finiteHorizon_converges_to_stationary
-- name    : RobustMDP.Stationarity.finiteHorizon_converges_to_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:25:58.914569+00:00
-- url     : https://prove2.me/theorems/6a52f756-782d-4e45-93e8-7534478e8939
-- title:
--   Eq. (33), p. 786 — the finite-horizon robust value converges to the stationary game value $\phi_\infty(\Pi_s,\mathcal T_s)$
-- statement:
--   In a robust discounted MDP with discount factor $0<\nu<1$ (finite states, finite nonempty action set, costs $c\ge0$, nonempty rectangular row sets in the simplex): for every $\varepsilon>0$ there is $N_\varepsilon$ such that for every $N>N_\varepsilon$
--   $$
--   \phi_\infty(\Pi_s,\mathcal T_s)-\varepsilon\le\phi_N(\Pi,\mathcal T)\le\phi_\infty(\Pi_s,\mathcal T_s).
--   $$
--   In particular the finite-horizon robust value under time-varying uncertainty, $\phi_N(\Pi,\mathcal T)$, converges to the value of the stationary infinite-horizon game (6).
--
--   This is Step (a) of the proof of Theorem 4; combined with Eq. (35) it yields $\phi_\infty(\Pi,\mathcal T)=\phi_\infty(\Pi_s,\mathcal T_s)$.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 786, Eq. (33) (proof of Theorem 4, Step (a))

import Mathlib
import Definitions.Def_RobustMDP_Stationarity_Model
import Definitions.Def_RobustMDP_Stationarity_gameValues

namespace RobustMDP.Stationarity

/-- Nilim–El Ghaoui 2005, p. 786, Step (a), Eq. (33): for every `ε > 0` there is `N_ε` such that
for every `N > N_ε`, `φ_∞(Π_s, 𝒯_s) - ε ≤ φ_N(Π, 𝒯) ≤ φ_∞(Π_s, 𝒯_s)`; in particular
`φ_N(Π, 𝒯) → φ_∞(Π_s, 𝒯_s)`. -/
theorem finiteHorizon_converges_to_stationary {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n) :
    ∀ ε > 0, ∃ Nε : ℕ, ∀ N > Nε,
      M.phiInf_PsTs ν i₀ - ε ≤ M.phiN_PT ν i₀ N ∧ M.phiN_PT ν i₀ N ≤ M.phiInf_PsTs ν i₀ := by sorry

end RobustMDP.Stationarity
