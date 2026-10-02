-- Prove2me | Theorems.Thm_ServiceParts_BaseStock_property_a
-- name    : ServiceParts.BaseStock.property_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:34:00.246157+00:00
-- url     : https://prove2.me/theorems/439d217a-fd36-4b7c-bb47-8c4bae109666
-- title:
--   Property (a) — order-up-to levels are nondecreasing in the horizon
-- statement:
--   In the model of Section 2.1 with lead time one period, let $n \ge 2$. If the order-up-to rule with real level $s$ is optimal in the $n$-period problem and the order-up-to rule with real level $s'$ is optimal in the $(n+1)$-period problem, then
--   $$
--   s \le s' .
--   $$
--   In the book's notation, $s_n^* \le s_{n+1}^*$: the longer the remaining horizon, the higher the stock level ordered up to.
--
--   **Formalization Note** The book derives (a) from its property (d), $f_n' \le f_{n-1}'$, which is false as printed (see the mission description); property (a) itself holds and is stated here for any optimal real levels, so no uniqueness of the level is presupposed.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 18, Section 2.1, proof of Theorem 2 (property (a)); re-established p. 20

import Mathlib
import Definitions.Def_ServiceParts_BaseStock_Model
import Definitions.Def_ServiceParts_BaseStock_Recursion

open MeasureTheory Set Filter Topology

namespace ServiceParts.BaseStock

/-- Property (a) in the proof of Theorem 2, p. 18 (sₙ* ≥ sₙ₋₁*): for n ≥ 2, if the
order-up-to rule with level s is optimal in the n-period problem and the order-up-to rule
with level s' is optimal in the (n + 1)-period problem, then s ≤ s'. -/
theorem property_a (M : Model) (n : ℕ) (hn : 2 ≤ n) (s s' : ℝ)
    (hs : M.IsOrderUpToOptimal n s) (hs' : M.IsOrderUpToOptimal (n + 1) s') : s ≤ s' := by sorry

end ServiceParts.BaseStock
