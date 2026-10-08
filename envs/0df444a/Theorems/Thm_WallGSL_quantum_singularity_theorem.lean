-- Prove2me | Theorems.Thm_WallGSL_quantum_singularity_theorem
-- name    : WallGSL.quantum_singularity_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-04T22:25:09.977651+00:00
-- url     : https://prove2.me/theorems/fc474b0f-045b-43a6-b3a7-65ea4ed3c471
-- title:
--   Theorem 4 (Wall 2013): the GSL implies a quantum singularity theorem
-- statement:
--   **Theorem 4 (quantum singularity theorem).** Let $(M,g)$ be a time-oriented Lorentzian spacetime, $C^\infty$, Hausdorff and second countable, and let $S_{\rm gen}$ be a generalized entropy assigning a real number to every region of $M$. Assume:
--
--   1. $M$ is **globally hyperbolic**: no closed timelike curves, and $J^+(p)\cap J^-(q)$ is compact for all $p,q$;
--   2. $T$ is a **quantum trapped surface**: $T$ is the nonempty compact boundary, inside a connected Cauchy surface $\Sigma$, of a relatively open exterior region $\mathrm{Ext}\subseteq\Sigma$ with noncompact closure, and the generalized entropy outside the null surface $N$ shot outwards and to the future from $T$ is decreasing at every point of $T$;
--   3. the **semiclassical approximation holds near $T$**, in the form of the comparison principle of Theorem 1 at every point $g_0\in T$, comparing $N$ against causal horizons;
--   4. the **fine-grained GSL** holds: for every observer $W$ and Cauchy surfaces $\Sigma'$ nowhere to the past of $\Sigma$,
--   $$S_{\rm gen}(\Sigma'\cap I^-(W))\ \ge\ S_{\rm gen}(\Sigma\cap I^-(W)).$$
--
--   Then
--   $$M \text{ is not null geodesically complete,}$$
--   i.e. there is a singularity somewhere.
--
--   This is the quantum analogue of Penrose's singularity theorem, with the null energy condition replaced by the generalized second law. It is the main result of the paper and the goal of this mission.
--
--   **Formalization Note** The generalized entropy is an arbitrary function `Sgen : Set M → ℝ`; all physical input is in hypotheses 2–4 (see the definition files). Hausdorffness and second countability are the field's standing conventions for spacetimes.
-- source:
--   A. C. Wall, The generalized second law implies a quantum singularity theorem, Class. Quantum Grav. 30 (2013) 165003, https://doi.org/10.1088/0264-9381/30/16/165003, §3.2, Theorem 4, p. 15

import Definitions.Def_WallGSL_GeneralizedEntropy

open scoped Manifold Topology ContDiff
open Set

namespace WallGSL

/-- Theorem 4 of Wall (2013): a globally hyperbolic spacetime containing a quantum
trapped surface `T`, near which the semiclassical approximation holds, and in which the
fine-grained GSL holds, is not null geodesically complete. -/
theorem quantum_singularity_theorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (st : LorentzianMetric E M) (Sgen : Set M → ℝ) (S T Ext : Set M)
    (hGH : st.IsGloballyHyperbolic)
    (hT : st.IsQuantumTrappedSurface Sgen S T Ext)
    (hSC : ∀ g₀ ∈ T, st.TheoremOneComparisonAt Sgen
      (st.outgoingNullSurface S T Ext) (st.outgoingExterior S Ext) g₀)
    (hGSL : st.FineGrainedGSL Sgen) :
    ¬ st.IsNullGeodesicallyComplete := by sorry

end WallGSL
