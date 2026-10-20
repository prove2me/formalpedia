-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P35_generalizedMean_iff_dataProcessing
-- name    : QAlgorithms.Papers.Independent.Dependency50.P35.generalizedMean_iff_dataProcessing
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:51:27.408128+00:00
-- url     : https://prove2.me/theorems/245753dc-417a-45db-8447-4ac27ea0c439
-- title:
--   Proposition 1: generalized-mean convexity iff data processing
-- statement:
--   Let $D$ be one real-valued divergence family on all finite-dimensional complex spaces, defined on positive semidefinite pairs $(\rho,\sigma)$ with $\rho\ne0$ and $\ker\sigma\subseteq\ker\rho$. Suppose it satisfies continuity on this domain, unitary invariance, $D(1\|1/2)=1$, both directions of the order axiom, tensor additivity, and the trace-weighted generalized-mean axiom with a single continuous strictly monotonic generator $g$. Then
--
--   $$
--   \text{$g\circ D$ is jointly convex on normalized pairs if $g$ increases, or jointly concave if $g$ decreases}
--   \quad\Longleftrightarrow\quad
--   D(\mathcal E(\rho)\|\mathcal E(\sigma))\le D(\rho\|\sigma)
--   \text{ for every CPTP map }\mathcal E.
--   $$
--
--   All joint comparisons lie in the domain of $D$, and channels may change dimension. This characterizes data processing within the source's axiomatic framework.
-- source:
--   On quantum Renyi entropies: a new generalization and some properties, arXiv:1306.3142v4, PDF p. 5, Proposition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Filter Topology

namespace QAlgorithms.Papers.Independent.Dependency50.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Reuse the accepted matrix type and positive-operator Schatten expression.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat schatten)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

/-- PDF p.5, Proposition 1. The six axioms are hypotheses, not properties assumed
of the particular sandwiched divergence. D is a single family across dimensions. -/
theorem generalizedMean_iff_dataProcessing (D : DivergenceFamily) (g : ℝ → ℝ)
    (h : SixAxioms D g) : GeneralMeanConvexity D g ↔ FamilyDPI D := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P35

end
