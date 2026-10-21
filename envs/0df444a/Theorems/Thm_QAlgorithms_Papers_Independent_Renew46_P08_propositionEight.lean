-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_propositionEight
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.propositionEight
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:06:34.191911+00:00
-- url     : https://prove2.me/theorems/ffc4dd80-9a5e-42ab-afa6-617135be4f92
-- title:
--   Proposition 8, (74): generalized-ensemble local continuity
-- statement:
--   Let $\mu_n$ be Borel probability measures on the trace-norm state space, weakly converging to $\mu_0$. If the entropies of their actual barycenters satisfy $H(\overline\rho(\mu_n))\to H(\overline\rho(\mu_0))<\infty$, then
--
--   $$\chi(\mu_n)\longrightarrow\chi(\mu_0)<\infty.$$
--
--   Here chi is the integral of relative entropy to the barycenter. Non-atomic ensembles are included; finite entropy is imposed at the limiting barycenter, rather than as an artificial assumption on each signal.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 31, Proposition 8, (74): generalized-ensemble local continuity

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

/-- Proposition 8, PDF pp.30–31, (74): arbitrary Borel laws, including non-atomic
ones; finite entropy is needed only at the limiting barycenter. -/
theorem propositionEight {I : Type} [Countable I] [Nonempty I]
    (mu : ℕ → GeneralizedEnsemble I) (mu0 : GeneralizedEnsemble I)
    (hweak : Tendsto mu atTop (nhds mu0))
    (hH : Tendsto (fun n => extendedEntropyNats (averageCoefficients (mu n)))
      atTop (nhds (extendedEntropyNats (averageCoefficients mu0))))
    (hfinite : extendedEntropyNats (averageCoefficients mu0) < ⊤) :
    Tendsto (fun n => ensembleHolevo id (mu n)) atTop (nhds (ensembleHolevo id mu0)) ∧
      ensembleHolevo id mu0 < ⊤ := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
