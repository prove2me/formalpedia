-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_propositionFour
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.propositionFour
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:58:07.326996+00:00
-- url     : https://prove2.me/theorems/0d7f31ba-37c2-4c65-b942-e497c9f0a69f
-- title:
--   Proposition 4, (58): ensemble metric topologies
-- statement:
--   For countable ensembles on the trace-norm state space, the distances $D_*$ and $D_K$ both generate weak convergence. Precisely, for a sequence $\mu_n=\{p_i^n,\rho_i^n\}$ and limit $\mu_0$,
--
--   $$D_*(\mu_n,\mu_0)\to0\ \Longleftrightarrow\ \sum_i p_i^n f(\rho_i^n)\to\sum_i p_i^0f(\rho_i^0)\quad(\text{every bounded continuous real }f),$$
--
--   and the same equivalence holds for $D_K$. This is equality of convergence topologies, not equality of the distances; $D_0$ is excluded.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 23, Proposition 4, (58): ensemble metric topologies

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

/-- Proposition 4, PDF p.23, (58): equality of sequential convergence topologies,
not equality of Dstar and DK distances. D0 is not in this equivalence. -/
theorem propositionFour {I : Type} [Countable I] [Nonempty I]
    (mu : ℕ → CountableStateEnsemble I) (mu0 : CountableStateEnsemble I) :
    (Tendsto (fun n => distanceStar (mu n) mu0) atTop (nhds 0) ↔ WeakConverges mu mu0) ∧
    (Tendsto (fun n => distanceK (mu n) mu0) atTop (nhds 0) ↔ WeakConverges mu mu0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
