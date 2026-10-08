-- Prove2me | Theorems.Thm_Sennott1989_AvgCost_queue_value_monotone
-- name    : Sennott1989.AvgCost.queue_value_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:05.114474+00:00
-- url     : https://prove2.me/theorems/cbe7a3b5-a438-459a-9877-8222b6c5f1b0
-- title:
--   §3, proof of Proposition 8, p. 631 — V_α(i) is increasing in i, hence Assumption 2 holds
-- statement:
--   For the queueing model with variable service rates of Example 2 under the cost structure of p. 631 (so that $C(i,a)$ is increasing in $i$ for every $a$), and for every discount factor $\alpha\in(0,1)$:
--
--   1. the $n$-horizon discounted value $V_{\alpha,n}(i)$ (terminal cost $0$) is increasing in $i$ for every $n$;
--   2. the discounted value $V_\alpha(i)$ is increasing in $i$;
--   3. consequently, under Assumption 1, Assumption 2 holds with $N=0$: $h_\alpha(i)=V_\alpha(i)-V_\alpha(0)\ge0$ for all $i$ and $\alpha$.
--
--   This is the step of the proof of Proposition 8 that supplies Assumption 2.
--
--   **Formalization Note** Values are in $[0,\infty]$; items 1–2 need no moment assumption. $V_{\alpha,n}$ is the $n$-horizon value of the Sennott (1999) development, which equals the paper's value iteration iterate. Since $h_\alpha$ is defined only when the values are finite, item 3 is stated under Assumption 1.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, §3, proof of Proposition 8, first paragraph, p. 631

import Mathlib
import Definitions.Def_Sennott1989_AvgCost_Assumptions
import Definitions.Def_Sennott1989_AvgCost_Queue

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

open SennottDP.Discounted

/-- Sennott (1989), §3, proof of Proposition 8, p. 631 (unnumbered). For the queueing model with
variable service rates of Example 2 under the cost structure of p. 631 (`C(i, a)` increasing in
`i` for every `a`), the structure of (13) gives that `V_{α,n}(i)` is increasing in `i` for every
`n`, and hence (Proposition 3) `V_α(i)` is increasing in `i`, for every discount factor
`α ∈ (0, 1)`. Therefore Assumption 2 holds (with `N = 0`).

**Formalization Note** `V_{α,n}` is `SennottDP.Discounted.finiteValueFn` (the `n`-horizon
discounted value with terminal cost `0`, which equals the paper's value iteration iterate) and
`V_α` is `SennottDP.Discounted.valueFn`, both in `[0, ∞]`; monotonicity holds there without any
moment assumption. Since `h_α(i) = V_α(i) − V_α(0)` is defined only under Assumption 1 (see
`relValue`), the conclusion "Assumption 2 holds" is stated under Assumption 1. -/
theorem queue_value_monotone {Act : Type} [Fintype Act] [Nonempty Act] (q : QueueData Act) :
    (∀ α : ℝ≥0, 0 < α → α < 1 → ∀ n : ℕ, Monotone fun i : ℕ => finiteValueFn q.toMDC α n i) ∧
      (∀ α : ℝ≥0, 0 < α → α < 1 → Monotone fun i : ℕ => valueFn q.toMDC α i) ∧
      (Assumption1 q.toMDC → Assumption2 q.toMDC 0) := by sorry

end Sennott1989.AvgCost
