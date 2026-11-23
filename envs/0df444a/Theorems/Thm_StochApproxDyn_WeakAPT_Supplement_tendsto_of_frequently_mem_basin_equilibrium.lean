-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_Supplement_tendsto_of_frequently_mem_basin_equilibrium
-- name    : StochApproxDyn.WeakAPT.Supplement.tendsto_of_frequently_mem_basin_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:13:22.74952+00:00
-- url     : https://prove2.me/theorems/48ab1e7b-9f14-4556-89f8-2230cd0b0560
-- title:
--   Theorem 6.9 — an asymptotic pseudotrajectory returning to a compact subset of the basin of an asymptotically stable equilibrium converges to it
-- statement:
--   Let $\Phi$ be a semiflow on a locally compact metric space $(M,d)$ and let $X:\mathbb R_+\to M$ be an asymptotic pseudotrajectory of $\Phi$: $X$ is continuous and $\lim_{t\to\infty}\sup_{0\le h\le T}d(X(t+h),\Phi_h(X(t)))=0$ for every $T>0$. Let $e$ be an **asymptotically stable equilibrium**, i.e. an equilibrium such that $\{e\}$ is an attractor, with basin of attraction $W$, and let $K\subseteq W$ be compact. If $X(t_k)\in K$ for some sequence $t_k\to\infty$, then
--
--   $$\lim_{t\to\infty}X(t)=e.$$
--
--   The hypothesis asks only for recurrent visits to a compact part of the basin, not for precompactness of the whole path. In the stochastic approximation setting this is the convergence theorem of Kushner and Clark (1978).
--
--   **Formalization Note** The semiflow is a Mathlib `Flow ℝ≥0 M`; a flow enters through its forward semiflow. Asymptotic pseudotrajectories, attractors and basins are the published definitions of this series.
--
--   Differences from the source:
--   - encoding: "a flow or semiflow" → a semiflow `Flow ℝ≥0 M`; reason: only $t\ge0$ enters the statement, and a flow is used through its restriction to $t\ge0$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 28, Theorem 6.9 (standing assumption: M locally compact, p. 28; attractor and asymptotic stability, p. 22)

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_AsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_LimitSet_Attractor

open scoped NNReal
open Filter

namespace StochApproxDyn.WeakAPT.Supplement

/-- Theorem 6.9 (Benaïm 1999, p. 28). Let `Φ` be a semiflow on a locally compact metric space `M`
and `X` an asymptotic pseudotrajectory of `Φ`. Let `e` be an asymptotically stable equilibrium
(an equilibrium `e` such that `{e}` is an attractor, p. 22) with basin of attraction `W`, and let
`K ⊆ W` be compact. If `X(t_k) ∈ K` for some sequence `t_k → ∞`, then `X(t) → e` as `t → ∞`. -/
theorem tendsto_of_frequently_mem_basin_equilibrium {M : Type*} [MetricSpace M]
    [LocallyCompactSpace M] (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → M)
    (hX : StochApproxDyn.LimitSet.IsAsymptoticPseudotrajectory Φ X) (e : M)
    (he : StochApproxDyn.LimitSet.IsAttractor Φ {e}) (K : Set M) (hK : IsCompact K)
    (hKW : K ⊆ StochApproxDyn.LimitSet.basin Φ {e}) (τ : ℕ → ℝ≥0)
    (hτ : Tendsto τ atTop atTop) (hτK : ∀ k, X (τ k) ∈ K) :
    Tendsto X atTop (nhds e) := by sorry

end StochApproxDyn.WeakAPT.Supplement
