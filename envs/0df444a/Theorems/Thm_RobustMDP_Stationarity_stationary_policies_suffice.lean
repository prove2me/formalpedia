-- Prove2me | Theorems.Thm_RobustMDP_Stationarity_stationary_policies_suffice
-- name    : RobustMDP.Stationarity.stationary_policies_suffice
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:28:12.264193+00:00
-- url     : https://prove2.me/theorems/91e0dfbd-56b8-4c56-9d3b-fc21134b80ba
-- title:
--   Theorem 4, p. 786 — stationary policies suffice, and the stationary/time-varying gap vanishes at rate $\nu$
-- statement:
--   Consider a robust discounted MDP: finite state space $\mathcal X$, finite nonempty action set $\mathcal A$, costs $c(i,a)\ge0$, nonempty rectangular row uncertainty sets $\mathcal P_i^a\subseteq\Delta_n$, initial state $i_0$ and discount factor $0<\nu<1$. Then:
--
--   1. In the infinite-horizon problem the control and nature policies may be taken stationary without loss of generality:
--   $$
--   \phi_\infty(\Pi,\mathcal T)=\phi_\infty(\Pi_s,\mathcal T_s)=\phi_\infty(\Pi_s,\mathcal T)=\phi_\infty(\Pi,\mathcal T_s).\qquad(31)
--   $$
--   2. In the finite-horizon problem with the discounted cost, the gap between the robust values under time-varying and stationary uncertainty vanishes at geometric rate $\nu$: for every horizon $N$,
--   $$
--   0\le\phi_N(\Pi,\mathcal T)-\phi_N(\Pi,\mathcal T_s)\le\frac{\nu^N c_{\max}}{1-\nu},\qquad c_{\max}=\max_{i,a}c(i,a).
--   $$
--
--   The stationary-uncertainty game (3) is the statistically natural model but is hard to solve, while the time-varying game (4) is solved by robust dynamic programming; part 2 quantifies how little is lost by solving (4) instead of (3) in the discounted case.
--
--   **Formalization Note** The paper's "goes to zero as the horizon length $N$ goes to infinity, at a geometric rate $\nu$" is stated with the explicit constant $c_{\max}/(1-\nu)$ that the paper's own proof produces (the $\varepsilon_N$ of Eq. (34)); the lower bound $0\le$ is inequality (4) of the paper. All min/max are infima/suprema of real numbers; attainment is not assumed.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 786, Theorem 4, Eq. (31)

import Mathlib
import Definitions.Def_RobustMDP_Stationarity_Model
import Definitions.Def_RobustMDP_Stationarity_gameValues

namespace RobustMDP.Stationarity

/-- Nilim–El Ghaoui 2005, p. 786, Theorem 4. In the infinite-horizon problem the control and nature
policies may be taken stationary, (31):
`φ_∞(Π, 𝒯) = φ_∞(Π_s, 𝒯_s) = φ_∞(Π_s, 𝒯) = φ_∞(Π, 𝒯_s)`; and in the discounted finite-horizon
problem the gap `φ_N(Π, 𝒯) - φ_N(Π, 𝒯_s)` goes to zero at geometric rate `ν`, in the explicit
form `0 ≤ φ_N(Π, 𝒯) - φ_N(Π, 𝒯_s) ≤ ν^N c_max / (1 - ν)` for every `N`. -/
theorem stationary_policies_suffice {n : ℕ} {A : Type} [Fintype A] [Nonempty A]
    (M : Model n A) (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n) :
    (M.phiInf_PT ν i₀ = M.phiInf_PsTs ν i₀ ∧
      M.phiInf_PsTs ν i₀ = M.phiInf_PsT ν i₀ ∧
      M.phiInf_PsT ν i₀ = M.phiInf_PTs ν i₀) ∧
    ∀ N : ℕ, 0 ≤ M.phiN_PT ν i₀ N - M.phiN_PTs ν i₀ N ∧
      M.phiN_PT ν i₀ N - M.phiN_PTs ν i₀ N ≤ ν ^ N * M.cmax / (1 - ν) := by sorry

end RobustMDP.Stationarity
