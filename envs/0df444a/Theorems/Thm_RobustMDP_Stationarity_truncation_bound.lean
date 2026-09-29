-- Prove2me | Theorems.Thm_RobustMDP_Stationarity_truncation_bound
-- name    : RobustMDP.Stationarity.truncation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:24:03.551453+00:00
-- url     : https://prove2.me/theorems/e2779824-4f61-4515-a463-d2dc0714ccc2
-- title:
--   Eq. (34), p. 786 — truncating the discounted cost at horizon $N$ loses at most $\nu^N c_{\max}/(1-\nu)$
-- statement:
--   Consider a robust discounted MDP with finite state space, finite nonempty action set, costs $c\ge0$, nonempty row sets $\mathcal P_i^a\subseteq\Delta_n$, and a discount factor $0<\nu<1$. Let $c_{\max}=\max_{i,a}c(i,a)$ and $\varepsilon_N=\nu^N c_{\max}/(1-\nu)$. Then for every controller policy $\pi\in\Pi$, every nature policy $\tau\in\mathcal T$ and every horizon $N$,
--   $$
--   C_N(\pi,\tau)\le C_\infty(\pi,\tau)\le C_N(\pi,\tau)+\varepsilon_N .
--   $$
--
--   This elementary bound is used in every step of the proof of Theorem 4: it transfers statements about finite-horizon values to infinite-horizon ones with an error that vanishes at geometric rate $\nu$.
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 786, Eq. (34) (proof of Theorem 4, Step (b))

import Mathlib
import Definitions.Def_RobustMDP_Stationarity_Model

namespace RobustMDP.Stationarity

/-- Nilim–El Ghaoui 2005, p. 786, Eq. (34): for every `N`, every controller policy `π ∈ Π` and
every nature policy `τ ∈ 𝒯`, `C_N(π, τ) ≤ C_∞(π, τ) ≤ C_N(π, τ) + ε_N` with
`ε_N = ν^N c_max / (1 - ν)`. -/
theorem truncation_bound {n : ℕ} {A : Type} [Fintype A] [Nonempty A] (M : Model n A)
    (ν : ℝ) (hν₀ : 0 < ν) (hν₁ : ν < 1) (i₀ : Fin n)
    (π : Policy n A) (τ : M.NaturePolicy) (N : ℕ) :
    M.finiteCost ν i₀ N π τ ≤ M.infCost ν i₀ π τ ∧
      M.infCost ν i₀ π τ ≤ M.finiteCost ν i₀ N π τ + M.epsN ν N := by sorry

end RobustMDP.Stationarity
