-- Prove2me | Theorems.Thm_TBSGStrategyIteration_exists_optimal_profile
-- name    : TBSGStrategyIteration.exists_optimal_profile
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T00:35:25.284327+00:00
-- url     : https://prove2.me/theorems/e246beca-9742-412a-b329-0a0e3ce694de
-- title:
--   Theorem 2.8 — existence and uniqueness of the value (Shapley)
-- statement:
--   Let $G$ be a 2-player turn-based discounted stochastic game. Then $G$ has an optimal strategy profile, and any two optimal profiles have the same value vector:
--   $$\exists\, \pi \in \Pi \text{ optimal}, \qquad \pi, \pi' \text{ optimal} \implies v_\pi = v_{\pi'} .$$
--   The common value vector is the **optimal value vector** $v^*$. This theorem is what makes the hypothesis on the counter-strategy map $\tau_2$ in the main theorem satisfiable: an optimal counter-strategy exists against every strategy.
-- source:
--   Hansen, Miltersen, Zwick, Strategy iteration is strongly polynomial for 2-player turn-based stochastic games with a constant discount factor, arXiv:1008.0530v1, p. 4, Theorem 2.8

import Mathlib
import Definitions.Def_TBSGStrategyIteration_IsOptimal

namespace TBSGStrategyIteration

/-- Theorem 2.8 (Shapley): every 2TBSG has an optimal strategy profile, and any two optimal
strategy profiles have the same value vector. -/
theorem exists_optimal_profile {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (G : Game S A) :
    (∃ π : Profile G, IsOptimal G π) ∧
      ∀ π π' : Profile G, IsOptimal G π → IsOptimal G π' → value G π = value G π' := by sorry

end TBSGStrategyIteration
