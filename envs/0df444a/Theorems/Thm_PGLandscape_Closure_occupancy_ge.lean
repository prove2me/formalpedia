-- Prove2me | Theorems.Thm_PGLandscape_Closure_occupancy_ge
-- name    : PGLandscape.Closure.occupancy_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:28:49.082931+00:00
-- url     : https://prove2.me/theorems/da556126-955d-4de1-aec3-a0f421d93c71
-- title:
--   §2, p. 7 — η_π ⪰ (1 − γ)ρ: the occupancy measure dominates the scaled initial distribution
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process and $\pi$ a measurable stationary policy, with discounted state-occupancy measure $\eta_\pi = (1-\gamma)\sum_{t\ge0}\gamma^t P^\pi_\rho(s_t\in\cdot)$. Then for every measurable set $B\subseteq\mathcal S$,
--   $$\eta_\pi(B)\ \ge\ (1-\gamma)\,\rho(B).$$
--
--   The inequality says that the occupancy measure of any policy sees every part of the state space that the initial distribution sees. It turns $\rho$-integrals of nonnegative quantities into lower bounds for $\eta_\pi$-integrals, the step that converts a statement about the weighted policy-iteration objective into one about the average Bellman error.
--
--   **Formalization Note** The page states it for $\pi\in\Pi$; the statement here holds for every measurable policy, feasible or not, and drops all other standing hypotheses, which makes it stronger. Both sides are measures with values in $[0,\infty]$.
-- source:
--   arXiv:1906.01786v3, §2, p. 7, paragraph after Assumption 1 (consequence of (2))

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.Closure

open MeasureTheory ProbabilityTheory

theorem occupancy_ge {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : MDP S A)
    (π : MPolicy S A) :
    ∀ B : Set S, MeasurableSet B → ENNReal.ofReal (1 - M.γ) * M.ρ B ≤ occupancy M π B := by sorry

end PGLandscape.Closure
