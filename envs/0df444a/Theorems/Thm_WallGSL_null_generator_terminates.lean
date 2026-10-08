-- Prove2me | Theorems.Thm_WallGSL_null_generator_terminates
-- name    : WallGSL.null_generator_terminates
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-04T21:18:12.722994+00:00
-- url     : https://prove2.me/theorems/ae62c021-a770-4087-8382-8a20dcf32985
-- title:
--   Theorem 3 (Wall 2013): null generators with decreasing generalized entropy terminate
-- statement:
--   **Theorem 3.** Let $(M,g)$ be a time-oriented Lorentzian spacetime ($C^\infty$, Hausdorff, second countable) with a generalized entropy $S_{\rm gen}$. Let $N$ be an achronal null surface with exterior region $X$, and let $g_0$ be a point at which the fine-grained generalized entropy of $X$ is **decreasing**: there is a Cauchy surface $\Sigma\ni g_0$ such that for every neighbourhood $U$ of $g_0$ the slice can be pushed forwards in time inside $U$ to $\Sigma'$ with
--   $$S_{\rm gen}(\Sigma'\cap X)<S_{\rm gen}(\Sigma\cap X).$$
--   Assume the semiclassical approximation holds near $g_0$ (in the form of the comparison principle of Theorem 1 at $g_0$) and the fine-grained GSL holds. Then no future-directed null geodesic ray $W$ starting at $g_0$ with infinite affine parameter stays on $N$ forever:
--   $$W([a,\infty))\not\subseteq N.$$
--   Equivalently, the null generator through $g_0$ must terminate when traced towards the future, either because it exits $N$ or because spacetime is null geodesically incomplete.
--
--   This is the thermodynamic half of the singularity theorem: the GSL forbids a surface whose generalized entropy decreases from being a horizon.
--
--   **Formalization Note** Achronality of $N$ is the property of null surfaces (boundaries of past or future sets) that the paper's proof uses when it states that the horizon $H$ lies on or to the past of $N$.
-- source:
--   A. C. Wall, The generalized second law implies a quantum singularity theorem, Class. Quantum Grav. 30 (2013) 165003, https://doi.org/10.1088/0264-9381/30/16/165003, §3.2, Theorem 3, pp. 14–15

import Definitions.Def_WallGSL_GeneralizedEntropy

open scoped Manifold Topology ContDiff
open Set

namespace WallGSL

/-- Theorem 3 of Wall (2013): if the fine-grained generalized entropy outside the
achronal null surface `N` is decreasing at `g₀`, the semiclassical comparison of
Theorem 1 holds at `g₀`, and the fine-grained GSL holds, then no future-directed null
geodesic ray starting at `g₀` with infinite affine parameter stays on `N` forever. -/
theorem null_generator_terminates
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (st : LorentzianMetric E M) (Sgen : Set M → ℝ) (N X : Set M) (g₀ : M)
    (hN : st.IsAchronal N)
    (hdec : st.EntropyDecreasingAt Sgen X g₀)
    (hSC : st.TheoremOneComparisonAt Sgen N X g₀)
    (hGSL : st.FineGrainedGSL Sgen)
    (W : ℝ → M) (a : ℝ) (hW : st.IsFutureInfiniteNullRay W a) (hWa : W a = g₀) :
    ¬ (W '' Ici a ⊆ N) := by sorry

end WallGSL
