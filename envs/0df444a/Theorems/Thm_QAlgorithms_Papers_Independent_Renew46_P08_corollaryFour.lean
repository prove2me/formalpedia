-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_corollaryFour
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.corollaryFour
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:58:59.522816+00:00
-- url     : https://prove2.me/theorems/9837d5d2-5a3d-4903-bdcb-bd42f8e73d8d
-- title:
--   Corollary 4: uniform continuity with finite dimension or bounded label count
-- statement:
--   Choose any one of $D_0,D_*,D_K$ on countable ensemble presentations. The Holevo quantity is finite and uniformly continuous on all ensembles if the Hilbert space is finite-dimensional, and is also finite and uniformly continuous on ensembles of at most $m$ labels for every fixed finite $m\ge1$, regardless of Hilbert-space dimension. Explicitly, on either such set $S$,
--
--   $$\forall\eta>0\ \exists\delta>0\ \forall\mu,\nu\in S,\quad D(\mu,\nu)<\delta\Longrightarrow|\chi(\mu)-\chi(\nu)|<\eta.$$
--
--   The two sufficient conditions are alternatives, not simultaneous requirements.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 25, Corollary 4: uniform continuity with finite dimension or bounded label count

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Renew46.P08

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble convexOperatorMixture)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity traceSize tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats
    extendedRelativeEntropyNats ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (partialTraceFirst partialTraceSecond operatorTrace)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P07
  (boundedCoefficients oscillatorGround oscillatorLevels oscillatorEnvelope oscillatorEntropyBounded)

open QAlgorithms.Papers.Independent.Next46.P08 (continuityRatio MajorantRegularity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Corollary 4, PDF p.25: finite dimension OR finite label bound suffices,
for each of the three specified distances, independently. -/
theorem corollaryFour {I : Type} [Countable I] [Nonempty I] :
    ∀ D : CountableStateEnsemble I → CountableStateEnsemble I → ℝ≥0∞,
      (D = distance0 ∨ D = distanceStar ∨ D = distanceK) →
      (Finite I → UniformChiOn D Set.univ) ∧
      (∀ m : ℕ, 0 < m → UniformChiOn D {mu | AtMostLabels m mu}) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
