-- Prove2me | Theorems.Thm_PGLandscape_GradDom_occupancy_ge
-- name    : PGLandscape.GradDom.occupancy_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:55.95882+00:00
-- url     : https://prove2.me/theorems/2f99836d-63e9-4510-971d-dbb2321cc3dd
-- title:
--   §2, p. 7 — by (2), η_π ⪰ (1 − γ)ρ for every stationary policy π
-- statement:
--   Let $\pi$ be a measurable stationary policy and $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\,\mathbb P^\pi_\rho(s_t\in\cdot)$ its discounted state-occupancy measure. Then for every measurable set $B\subseteq\mathcal S$,
--   $$\eta_\pi(B)\ \ge\ (1-\gamma)\,\rho(B).$$
--
--   The term $t=0$ of the series is $(1-\gamma)\rho$; the inequality is what converts $\rho$-weighted norms into $\eta_\pi$-weighted ones throughout the paper, for instance in step (c) of the proof of Theorem 2.
--
--   **Formalization Note** The statement holds for every measurable policy, feasible or not, which is slightly more general than the page's "$\pi\in\Pi$". Measures take values in $[0,\infty]$.
-- source:
--   arXiv:1906.01786v3, §2, paragraph after Assumption 1, p. 7

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.GradDom

open MeasureTheory ProbabilityTheory

/-- §2, p. 7 (from (2)): for every measurable stationary policy `π`, the discounted state-PGLandscape.Closure.occupancy
measure dominates `(1 − γ) ρ` element-wise, `η_π ⪰ (1 − γ) ρ`. -/
theorem occupancy_ge {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (π : PGLandscape.Closure.MPolicy S A) (B : Set S) (hB : MeasurableSet B) :
    ENNReal.ofReal (1 - M.γ) * M.ρ B ≤ PGLandscape.Closure.occupancy M π B := by sorry

end PGLandscape.GradDom
