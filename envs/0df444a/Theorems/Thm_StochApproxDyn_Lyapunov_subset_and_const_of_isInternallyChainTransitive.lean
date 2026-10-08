-- Prove2me | Theorems.Thm_StochApproxDyn_Lyapunov_subset_and_const_of_isInternallyChainTransitive
-- name    : StochApproxDyn.Lyapunov.subset_and_const_of_isInternallyChainTransitive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:12:33.1845+00:00
-- url     : https://prove2.me/theorems/12db0f23-6743-4a21-a4c8-9e54a44079b7
-- title:
--   Proposition 6.4 — if $V(\Lambda)$ has empty interior, every internally chain transitive set lies in $\Lambda$ and $V$ is constant on it
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $M$. Let $\Lambda\subset M$ be a compact invariant set and $V:M\to\mathbb R$ a Lyapounov function for $\Lambda$: $V$ is continuous, $t\mapsto V(\Phi_t(x))$ is constant for $x\in\Lambda$ and strictly decreasing for $x\in M\setminus\Lambda$. Assume that
--   $$\operatorname{int}V(\Lambda)=\emptyset\quad\text{in }\mathbb R .$$
--   Then every internally chain transitive set $L\subset M$ satisfies
--   $$L\subset\Lambda\qquad\text{and}\qquad V|_L\ \text{is constant}.$$
--
--   Combined with the limit set theorem (limit sets of precompact asymptotic pseudotrajectories are internally chain transitive), this is the tool that turns a Lyapounov function into a convergence result for stochastic approximation algorithms; for instance, by Sard's theorem it applies to stochastic gradient algorithms with $C^m$ potentials (Corollary 6.7). Remark 6.5 shows that the empty-interior hypothesis cannot be dropped.
--
--   **Formalization Note** The space $M$ is an arbitrary metric space and $\Phi$ a semiflow (`Flow ℝ≥0 M`). The conclusion quantifies over every internally chain transitive set, not only limit sets. Internally chain transitive sets are nonempty by definition; when $\Lambda=\emptyset$ no such set exists and the statement holds vacuously, as it does on the page.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 27, Proposition 6.4

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence
import Definitions.Def_StochApproxDyn_Lyapunov_LyapunovFunction

open scoped NNReal

namespace StochApproxDyn.Lyapunov

/-- Proposition 6.4 (Benaïm 1999, §6.2, p. 27). Let `Λ ⊂ M` be a compact invariant set of the
semiflow `Φ` and `V : M → ℝ` a Lyapounov function for `Λ`. Assume that `V(Λ) ⊂ ℝ` has empty
interior. Then every internally chain transitive set `L` is contained in `Λ` and `V` is constant
on `L`. -/
theorem subset_and_const_of_isInternallyChainTransitive {M : Type*} [MetricSpace M]
    (Φ : Flow ℝ≥0 M) (Λ : Set M) (V : M → ℝ) (hV : IsLyapunovFunction Φ Λ V)
    (hint : interior (V '' Λ) = ∅) :
    ∀ L : Set M, StochApproxDyn.LimitSet.IsInternallyChainTransitive Φ L →
      L ⊆ Λ ∧ ∃ v : ℝ, ∀ x ∈ L, V x = v := by sorry

end StochApproxDyn.Lyapunov
