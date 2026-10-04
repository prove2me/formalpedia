-- Prove2me | Theorems.Thm_StochApproxDyn_LimitSet_omegaLimitSet_isInternallyChainTransitive
-- name    : StochApproxDyn.LimitSet.omegaLimitSet_isInternallyChainTransitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:19:20.533457+00:00
-- url     : https://prove2.me/theorems/5012ea2c-0eb3-4170-af0b-b0ac1ab7bc31
-- title:
--   Corollary 5.6 — omega limit sets of precompact orbits are internally chain transitive
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $M$, not necessarily compact, and let $x\in M$. If the closure of the forward orbit $\gamma^+(x)=\{\Phi_t(x):t\ge0\}$ is compact, then
--   $$\omega(x)\ \text{is internally chain transitive.}$$
--
--   This is the special case of the limit set theorem for a genuine trajectory $X(t)=\Phi_t(x)$, and it is applied to the translation semiflow in the proof of that theorem.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 24, Corollary 5.6

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Corollary 5.6 (Benaïm 1999, p. 24): for `x` in a (not necessarily compact) metric space `M`,
if the forward orbit `γ⁺(x) = {Φ_t(x) : t ≥ 0}` has compact closure, then the omega limit set
`ω(x)` is internally chain transitive. -/
theorem omegaLimitSet_isInternallyChainTransitive {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (x : M) (hx : IsCompact (closure (Set.range fun t : ℝ≥0 => Φ t x))) :
    IsInternallyChainTransitive Φ (omegaLimitSet Φ x) := by sorry

end StochApproxDyn.LimitSet
