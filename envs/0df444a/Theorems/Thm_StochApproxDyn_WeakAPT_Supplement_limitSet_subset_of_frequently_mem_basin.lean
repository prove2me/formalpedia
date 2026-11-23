-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_Supplement_limitSet_subset_of_frequently_mem_basin
-- name    : StochApproxDyn.WeakAPT.Supplement.limitSet_subset_of_frequently_mem_basin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:13:50.895748+00:00
-- url     : https://prove2.me/theorems/77ec410b-2e79-4684-aaed-d86c0227d6b5
-- title:
--   Theorem 6.10 — an asymptotic pseudotrajectory returning to a compact subset of the basin of an attractor has its limit set in the attractor
-- statement:
--   Let $\Phi$ be a semiflow on a locally compact metric space $(M,d)$ and let $X:\mathbb R_+\to M$ be an asymptotic pseudotrajectory of $\Phi$. Let $A$ be an attractor of $\Phi$ (nonempty, compact, invariant, and attracting a neighbourhood of itself uniformly) with basin $W$, and let $K\subseteq W$ be compact. If $X(t_k)\in K$ for some sequence $t_k\to\infty$, then the limit set $L(X)=\bigcap_{t\ge0}\overline{X([t,\infty))}$ satisfies
--
--   $$L(X)\subseteq A.$$
--
--   This is the attractor version of Theorem 6.9; it is the deterministic statement behind the positive-probability convergence results of §7.
--
--   **Formalization Note** The semiflow is a Mathlib `Flow ℝ≥0 M`. Asymptotic pseudotrajectories, limit sets, attractors and basins are the published definitions of this series.
--
--   Differences from the source:
--   - encoding: "a flow or semiflow" → a semiflow `Flow ℝ≥0 M`; reason: only $t\ge0$ enters the statement, and a flow is used through its restriction to $t\ge0$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 29, Theorem 6.10 (standing assumption: M locally compact, p. 28; attractor, p. 22; limit set, p. 24)

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_Attractor

open scoped NNReal
open Filter

namespace StochApproxDyn.WeakAPT.Supplement

/-- Theorem 6.10 (Benaïm 1999, p. 29). Let `Φ` be a semiflow on a locally compact metric space
`M` and `X` an asymptotic pseudotrajectory of `Φ`. Let `A` be an attractor with basin `W` and let
`K ⊆ W` be compact. If `X(t_k) ∈ K` for some sequence `t_k → ∞`, then the limit set
`L(X) = ⋂_{t ≥ 0} closure X([t, ∞))` is contained in `A`. -/
theorem limitSet_subset_of_frequently_mem_basin {M : Type*} [MetricSpace M]
    [LocallyCompactSpace M] (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → M)
    (hX : StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory Φ X) (A : Set M)
    (hA : StochApproxDyn.LimitSet.IsAttractor Φ A) (K : Set M) (hK : IsCompact K)
    (hKW : K ⊆ StochApproxDyn.LimitSet.basin Φ A) (τ : ℕ → ℝ≥0)
    (hτ : Tendsto τ atTop atTop) (hτK : ∀ k, X (τ k) ∈ K) :
    StochApproxDyn.LimitSet.limitSet X ⊆ A := by sorry

end StochApproxDyn.WeakAPT.Supplement
