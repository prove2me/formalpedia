-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_remarkSixAttainment
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.remarkSixAttainment
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:57:25.729516+00:00
-- url     : https://prove2.me/theorems/bd056798-fcc3-45bd-841a-3739e8515f2a
-- title:
--   Remark 6, first clause: finite presentation attainment
-- statement:
--   If ensembles $\mu,\nu$ have presentations with at most $m,n\ge1$ labels, respectively, there exist equivalent presentations $\mu',\nu'$, each with at most $mn$ labels, such that
--
--   $$D_0(\mu',\nu')=D_*(\mu,\nu).$$
--
--   Equivalent means equality of their atomic state probability laws. This is finite-presentation attainment, including repeated signals and zero padding; it asserts no attainment for arbitrary infinite ensembles and no linear-program reduction.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 22, Remark 6, first clause: finite presentation attainment

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

/-- Remark 6, first clause, PDF p.22: finite presentations attain the factor
infimum in at most mn common labels. No infinite-presentation attainment or LP claim. -/
theorem remarkSixAttainment {I : Type} [Countable I] [Nonempty I]
    (mu nu : CountableStateEnsemble I) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmu : AtMostLabels m mu) (hnu : AtMostLabels n nu) :
    ∃ a b : CountableStateEnsemble I, ensembleLaw a = ensembleLaw mu ∧ ensembleLaw b = ensembleLaw nu ∧
      AtMostLabels (m*n) a ∧ AtMostLabels (m*n) b ∧ distance0 a b = distanceStar mu nu := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
