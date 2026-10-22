-- Prove2me | Theorems.Thm_TBSGStrategyIteration_sum_value_sub_eq_flux_modCost
-- name    : TBSGStrategyIteration.sum_value_sub_eq_flux_modCost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:01:19.471885+00:00
-- url     : https://prove2.me/theorems/f1526693-575a-4b95-bc89-0bf43e7f7528
-- title:
--   Lemma 3.12 — $e^T(v_{\pi'} - v_\pi) = x_{\pi'} (c^\pi)_{\pi'}$
-- statement:
--   For every two strategy profiles $\pi', \pi$,
--   $$e^T (v_{\pi'} - v_\pi) = x_{\pi'} (c^\pi)_{\pi'}, \quad\text{i.e.}\quad \sum_{i \in S} \big((v_{\pi'})_i - (v_\pi)_i\big) = \sum_{i \in S} (x_{\pi'})_i \, (c^\pi)_{\pi'(i)},$$
--   where $(c^\pi)_{\pi'} \in \mathbb{R}^n$ is the modified cost vector $c^\pi$ restricted to the actions of $\pi'$.
--
--   **Formalization Note.** The printed statement quantifies only over $\pi$; $\pi'$ is equally arbitrary, and the Lean statement quantifies over both.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 6, Lemma 3.12

import Mathlib
import Definitions.Def_TBSGStrategyIteration_flux
import Definitions.Def_TBSGStrategyIteration_modCost

namespace TBSGStrategyIteration

/-- Lemma 3.12: for every two strategy profiles `π', π`,
`eᵀ (v_{π'} − v_π) = x_{π'} (c^π)_{π'}`, i.e.
`∑_i ((v_{π'})_i − (v_π)_i) = ∑_i (x_{π'})_i (c^π)_{π'(i)}`.
(The printed statement quantifies only over `π`; `π'` is equally arbitrary.) -/
theorem sum_value_sub_eq_flux_modCost {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) (π' π : Profile G) :
    ∑ i, (value G π' i - value G π i) = ∑ i, flux G π' i * modCost G π (π'.act i) := by sorry

end TBSGStrategyIteration
