-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_holevoDiscontinuity
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.holevoDiscontinuity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T02:59:29.825322+00:00
-- url     : https://prove2.me/theorems/16fff6b2-c7c4-4075-897a-0dd6298607bd
-- title:
--   Unnumbered discontinuity on all countable ensembles
-- statement:
--   On an infinite-dimensional separable complex Hilbert system, the extended Holevo quantity is not continuous on all countable ensembles, for any of $D_0,D_*,D_K$. Equivalently, for each such distance,
--
--   $$\neg\bigl[\forall\mu_n,\mu_0,\ D(\mu_n,\mu_0)\to0\ \Longrightarrow\ \chi(\mu_n)\to\chi(\mu_0)\bigr].$$
--
--   This concerns the unrestricted set of countable ensembles. It does not contradict uniform continuity at a fixed finite bound on label count.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 25, Unnumbered discontinuity on all countable ensembles

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

/-- PDF pp.25–26: chi fails continuity on ALL countable ensembles in infinite
dimension, for each distance. Sequential continuity is equivalent here. -/
theorem holevoDiscontinuity {I : Type} [Countable I] [Infinite I] :
    ∀ D : CountableStateEnsemble I → CountableStateEnsemble I → ℝ≥0∞,
      (D = distance0 ∨ D = distanceStar ∨ D = distanceK) →
      ¬ (∀ (mu : ℕ → CountableStateEnsemble I) (mu0 : CountableStateEnsemble I),
        Tendsto (fun n => D (mu n) mu0) atTop (nhds 0) →
        Tendsto (fun n => countableHolevo (mu n)) atTop (nhds (countableHolevo mu0))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
