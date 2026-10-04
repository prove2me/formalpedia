-- Prove2me | Theorems.Thm_SennottDP_DiscountedASM_dc_of_bounded_cost
-- name    : SennottDP.DiscountedASM.dc_of_bounded_cost
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T07:49:16.550271+00:00
-- url     : https://prove2.me/theorems/6e77ec2d-7fab-4794-a11c-001dbdb446d1
-- title:
--   Proposition 4.7.1 — bounded costs imply DC($\alpha$)
-- statement:
--   Let $\Delta$ be an MDC with countable state space, $(\Delta_N)_{N\ge N_0}$ an approximating sequence for $\Delta$, and $\alpha\in(0,1)$. Assume there is a finite constant $B$ with
--   $$
--   C(i,a)\le B\qquad\text{for all states } i \text{ and actions } a\in A_i.
--   $$
--   Then Assumption DC($\alpha$) holds.
--
--   For bounded costs the approximating sequence method therefore always works: by Theorem 4.6.3 the values $V^N_\alpha$ converge to $V_\alpha$ and limit points of optimal policies of $\Delta_N$ are optimal for $\Delta$, for every approximating sequence.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 77, Proposition 4.7.1

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC
import Definitions.Def_SennottDP_DiscountedASM_ApproxSeq

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.DiscountedASM

/-- Proposition 4.7.1 (p. 77): if the costs are bounded, `C(i,a) ≤ B` for all state–action
pairs, then DC(α) holds. -/
theorem dc_of_bounded_cost {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (hB : ∃ B : ℝ≥0, ∀ i, ∀ a ∈ M.A i, M.C i a ≤ B) :
    Δs.DC α := by sorry

end SennottDP.DiscountedASM
