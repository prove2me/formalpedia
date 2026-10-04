-- Prove2me | Theorems.Thm_StochApproxDyn_LimitSet_internallyChainTransitive_tfae
-- name    : StochApproxDyn.LimitSet.internallyChainTransitive_tfae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:20:31.601977+00:00
-- url     : https://prove2.me/theorems/3d76cb47-7f96-4b5d-82f1-71de611c89db
-- title:
--   Proposition 5.3 — internally chain transitive $\iff$ connected and internally chain recurrent $\iff$ no proper attractor
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $M$ and let $\Lambda\subset M$ be nonempty. The following assertions are equivalent:
--
--   1. $\Lambda$ is internally chain transitive;
--   2. $\Lambda$ is connected and internally chain recurrent;
--   3. $\Lambda$ is a compact invariant set and $\Phi|\Lambda$ admits no proper attractor, that is, the only attractor of the restricted semiflow $\Phi|\Lambda$ is $\Lambda$ itself.
--
--   $$\text{(1)}\iff\text{(2)}\iff\text{(3)}.$$
--
--   The proposition, originally due to Bowen, makes precise the relation between chain transitivity, chain recurrence and attractors; criterion (2) is how Corollary 5.6 and the limit set theorem are proved.
--
--   **Formalization Note** The hypothesis $\Lambda\ne\emptyset$ is added: internally chain transitive and internally chain recurrent sets are nonempty by definition (the source introduces them for "a nonempty invariant set"), while for $\Lambda=\emptyset$ assertion (3) would hold vacuously. Connectedness is Mathlib's `IsConnected`, which includes nonemptiness. In (3) the attractors are those of the semiflow $\Phi|\Lambda$ on the subspace $\Lambda$; neighbourhoods are taken in $\Lambda$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 23, Proposition 5.3

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence
import Definitions.Def_StochApproxDyn_LimitSet_Attractor

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Proposition 5.3 (Benaïm 1999, p. 23), for a nonempty `Λ ⊂ M`. The following are equivalent:
(i) `Λ` is internally chain transitive; (ii) `Λ` is connected and internally chain recurrent;
(iii) `Λ` is a compact invariant set and `Φ|Λ` admits no proper attractor (every attractor of the
restricted semiflow is all of `Λ`). -/
theorem internallyChainTransitive_tfae {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (Λ : Set M) (hΛ : Λ.Nonempty) :
    List.TFAE
      [IsInternallyChainTransitive Φ Λ,
       IsConnected Λ ∧ IsInternallyChainRecurrent Φ Λ,
       IsCompact Λ ∧ ∃ h : IsInvariantSet Φ Λ,
         ∀ A : Set Λ, IsAttractor (restrictSemiflow Φ h) A → A = Set.univ] := by sorry

end StochApproxDyn.LimitSet
