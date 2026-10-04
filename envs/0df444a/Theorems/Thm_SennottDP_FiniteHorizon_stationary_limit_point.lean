-- Prove2me | Theorems.Thm_SennottDP_FiniteHorizon_stationary_limit_point
-- name    : SennottDP.FiniteHorizon.stationary_limit_point
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T06:35:00.316069+00:00
-- url     : https://prove2.me/theorems/e3db978e-0b94-443b-9170-229d86570095
-- title:
--   Proposition B.3 — every sequence of stationary policies has a limit point
-- statement:
--   Let $\Delta$ be an MDC with countable state space $S$ and finite action sets. Every sequence $(f_r)$ of stationary policies for $\Delta$ has at least one limit point: there are a stationary policy $f$ and a subsequence $(f_{r_k})$ such that for each $i \in S$,
--   $$
--   f_{r_k}(i) = f(i) \quad \text{for all sufficiently large } k.
--   $$
--
--   Countability of $S$ and finiteness of the $A_i$ are both essential. The result is the compactness statement behind every limit-of-optimal-policies argument in the book.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 289, Proposition B.3 (Definition B.1, pp. 288–289)

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.FiniteHorizon

/-- Proposition B.3 (Sennott, p. 289). Every sequence of stationary policies for `Δ` (countable
state space, finite action sets) has at least one limit point (Definition B.1). -/
theorem stationary_limit_point {S Act : Type} [Countable S] (M : MDC S Act)
    (fs : ℕ → M.Stationary) : ∃ f : M.Stationary, M.IsLimitPoint fs f := by sorry

end SennottDP.FiniteHorizon
