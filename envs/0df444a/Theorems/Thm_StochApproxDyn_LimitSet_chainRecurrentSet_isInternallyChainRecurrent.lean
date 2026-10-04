-- Prove2me | Theorems.Thm_StochApproxDyn_LimitSet_chainRecurrentSet_isInternallyChainRecurrent
-- name    : StochApproxDyn.LimitSet.chainRecurrentSet_isInternallyChainRecurrent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:19:04.454977+00:00
-- url     : https://prove2.me/theorems/fca37b4e-dff1-4510-b76f-a9b4fc21b7ca
-- title:
--   Theorem 5.5 — on a compact space, $R(\Phi)$ is internally chain recurrent
-- statement:
--   Let $\Phi$ be a semiflow on a nonempty compact metric space $M$, and let $R(\Phi)$ be its set of chain recurrent points. Then
--   $$R(\Phi)\ \text{is internally chain recurrent:}$$
--   it is compact and invariant, $\Phi_t(R(\Phi))=R(\Phi)$ for all $t\ge0$, and every point of $R(\Phi)$ is chain recurrent for the restricted semiflow $\Phi|R(\Phi)$, i.e. by pseudo-orbits that stay in $R(\Phi)$.
--
--   The theorem was proved by Conley for flows; it says that chain recurrence does not need excursions outside the chain recurrent set.
--
--   **Formalization Note** $M$ is assumed nonempty (`[Nonempty M]`), because internally chain recurrent sets are nonempty by definition; for $M=\emptyset$ the set $R(\Phi)$ is empty.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 23, Theorem 5.5

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Theorem 5.5 (Benaïm 1999, p. 23): if `M` is a (nonempty) compact metric space, the chain
recurrent set `R(Φ)` of a semiflow `Φ` on `M` is internally chain recurrent. -/
theorem chainRecurrentSet_isInternallyChainRecurrent {M : Type*} [MetricSpace M]
    [CompactSpace M] [Nonempty M] (Φ : Flow ℝ≥0 M) :
    IsInternallyChainRecurrent Φ (chainRecurrentSet Φ) := by sorry

end StochApproxDyn.LimitSet
