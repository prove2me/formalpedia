-- Prove2me | Theorems.Thm_PGLandscape_ApproxClosure_occupancy_ge
-- name    : PGLandscape.ApproxClosure.occupancy_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:51.299042+00:00
-- url     : https://prove2.me/theorems/faa3749b-cc59-4276-8146-f0be4ef7a09d
-- title:
--   §2, p. 7 — the occupancy measure dominates the initial distribution: η_π ⪰ (1 − γ)ρ
-- statement:
--   Let $\pi\in\Pi$ be a feasible measurable stationary policy, with discounted state-occupancy measure $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\,\mathbb P^\pi_\rho(s_t\in\cdot)$. For every measurable set $E\subseteq S$,
--
--   $$
--   \eta_\pi(E)\ge(1-\gamma)\rho(E),
--   $$
--
--   i.e. $\eta_\pi\succeq(1-\gamma)\rho$ element-wise. This transfers bounds on nonnegative integrands from the occupancy weighting to the initial distribution.
--
--   **Formalization Note** The feasibility hypothesis matches the page's $\pi\in\Pi$.
-- source:
--   arXiv:1906.01786v3, after (2), p. 7

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP
import Definitions.Def_PGLandscape_Closure_Conditions

namespace PGLandscape.ApproxClosure

open MeasureTheory ProbabilityTheory

/-- From (2), p. 7: the discounted occupancy measure of every feasible stationary policy
dominates `(1−γ)ρ` on every measurable set. -/
theorem occupancy_ge {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (π : PGLandscape.Closure.MPolicy S A) (hπ : PGLandscape.Closure.IsFeasible M π) :
    ∀ B : Set S, MeasurableSet B → ENNReal.ofReal (1 - M.γ) * M.ρ B ≤ PGLandscape.Closure.occupancy M π B := by sorry

end PGLandscape.ApproxClosure
