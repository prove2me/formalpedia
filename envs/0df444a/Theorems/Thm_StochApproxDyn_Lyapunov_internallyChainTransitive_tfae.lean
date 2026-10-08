-- Prove2me | Theorems.Thm_StochApproxDyn_Lyapunov_internallyChainTransitive_tfae
-- name    : StochApproxDyn.Lyapunov.internallyChainTransitive_tfae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T15:49:35.260988+00:00
-- url     : https://prove2.me/theorems/a76bb2b6-c0aa-4b16-a44f-5c98af1c93e7
-- title:
--   Proposition 5.3 — internally chain transitive $\iff$ connected and internally chain recurrent $\iff$ no proper attractor
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $M$ and let $\Lambda\subset M$ be nonempty. The following assertions are equivalent:
--
--   1. $\Lambda$ is internally chain transitive;
--   2. $\Lambda$ is connected and internally chain recurrent;
--   3. $\Lambda$ is a compact invariant set and $\Phi|\Lambda$ admits no proper attractor, i.e.
--   $$A\subset\Lambda \text{ an attractor of }\Phi|\Lambda\ \Longrightarrow\ A=\Lambda .$$
--
--   The proof of Proposition 6.4 uses (1) $\Rightarrow$ (3): an internally chain transitive set cannot contain a smaller attractor of its own restricted semiflow.
--
--   **Formalization Note** $\Lambda$ is assumed nonempty because the internal notions include nonemptiness, while (3) holds vacuously for $\Lambda=\emptyset$. Attractors of $\Phi|\Lambda$ are subsets of the subtype $\Lambda$ with its induced metric, and \"no proper attractor\" is \"every attractor equals the whole of $\Lambda$\".
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 23, Proposition 5.3

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence
import Definitions.Def_StochApproxDyn_LimitSet_Attractor

open scoped NNReal

namespace StochApproxDyn.Lyapunov

/-- Proposition 5.3 (Benaïm 1999, p. 23), for a nonempty `Λ ⊂ M`. The following are equivalent:
(i) `Λ` is internally chain transitive; (ii) `Λ` is connected and internally chain recurrent;
(iii) `Λ` is a compact invariant set and `Φ|Λ` admits no proper attractor (every attractor of the
restricted semiflow is all of `Λ`). -/
theorem internallyChainTransitive_tfae {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (Λ : Set M) (hΛ : Λ.Nonempty) :
    List.TFAE
      [StochApproxDyn.LimitSet.IsInternallyChainTransitive Φ Λ,
       IsConnected Λ ∧ StochApproxDyn.LimitSet.IsInternallyChainRecurrent Φ Λ,
       IsCompact Λ ∧ ∃ h : StochApproxDyn.LimitSet.IsInvariantSet Φ Λ,
         ∀ A : Set Λ, StochApproxDyn.LimitSet.IsAttractor (StochApproxDyn.LimitSet.restrictSemiflow Φ h) A → A = Set.univ] := by sorry

end StochApproxDyn.Lyapunov
