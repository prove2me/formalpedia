-- Prove2me | Theorems.Thm_TBSGStrategyIteration_flux_sum
-- name    : TBSGStrategyIteration.flux_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T00:53:55.525828+00:00
-- url     : https://prove2.me/theorems/208d7579-ef3f-4462-8d50-3455570bf0b5
-- title:
--   Lemma 3.10 — total flux $x_\pi e = n/(1-\gamma)$
-- statement:
--   For every strategy profile $\pi$, the entries of the flux vector sum to
--   $$x_\pi e = \sum_{i \in S} (x_\pi)_i = \frac{n}{1-\gamma},$$
--   where $e$ is the all-ones vector and $n = |S|$.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 6, Lemma 3.10

import Mathlib
import Definitions.Def_TBSGStrategyIteration_flux

namespace TBSGStrategyIteration

/-- Lemma 3.10: for every strategy profile `π`, the entries of the flux vector sum to
`x_π e = n / (1 − γ)`, where `n = |S|`. -/
theorem flux_sum {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (π : Profile G) :
    ∑ i, flux G π i = (Fintype.card S : ℝ) / (1 - G.γ) := by sorry

end TBSGStrategyIteration
