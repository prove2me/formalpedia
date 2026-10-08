-- Prove2me | Theorems.Thm_SennottDP_BOR_avgCost_eq_steadyState_discounted
-- name    : SennottDP.BOR.avgCost_eq_steadyState_discounted
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T11:29:47.251023+00:00
-- url     : https://prove2.me/theorems/377b0865-38f5-4653-8ece-50b8e405a791
-- title:
--   Lemma 7.5.2 — $J_d=(1-\alpha)\sum_{i\in R}\pi_i(d)V_{d,\alpha}(i)$
-- statement:
--   Let $d$ be a $z$ standard (randomized stationary) policy with positive recurrent class $R$, steady state probabilities $\pi_i(d)$ and average cost $J_d$. Then for every $\alpha\in(0,1)$
--   $$
--   J_d=(1-\alpha)\sum_{i\in R}\pi_i(d)V_{d,\alpha}(i).\qquad(7.32)
--   $$
--
--   The average cost of a standard policy is thus a convex combination of its normalized discounted costs over the recurrent class, which is how (SEN1) is verified.
--
--   **Formalization Note** $J_d$ is written as $J_d(i)$ for every initial state $i$ (it is constant for a $z$ standard policy, Proposition C.2.6(iii)); $R$ is the communicating class of $z$; all quantities are in $[0,\infty]$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 143, Lemma 7.5.2, (7.32)

import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Lemma 7.5.2, p. 143. If `d` is a `z` standard (randomized stationary) policy
with positive recurrent class `R`, then its average cost satisfies
`J_d = (1 − α) ∑_{i∈R} π_i(d) V_{d,α}(i)` for every `α ∈ (0,1)` (7.32). -/
theorem avgCost_eq_steadyState_discounted {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (d : RandStationaryPolicy M) (hd : IsZStandard d.toPolicy z) :
    ∀ α : ℝ, 0 < α → α < 1 → ∀ i,
      avgCost d.toPolicy i = ENNReal.ofReal (1 - α) *
        ∑' j : recClass M d z, steadyState d.toPolicy j * discCost d.toPolicy α j := by sorry

end SennottDP.BOR
