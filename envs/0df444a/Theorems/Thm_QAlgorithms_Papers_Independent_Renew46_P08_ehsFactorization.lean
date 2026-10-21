-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_ehsFactorization
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.ehsFactorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:56:13.281962+00:00
-- url     : https://prove2.me/theorems/e1f18031-a57e-42d2-bf2b-01d3f2b60be9
-- title:
--   Unnumbered equality of factor distance (53) and EHS (54)
-- statement:
--   For countable ensembles $\mu=\{p_i,\rho_i\}$ and $\nu=\{q_j,\sigma_j\}$, let $E(\mu)$ be all presentations of the same atomic probability law. Then
--
--   $$\inf_{\mu'\in E(\mu),\nu'\in E(\nu)}D_0(\mu',\nu')=\frac12\inf_{P,Q}\sum_{i,j}\|P_{ij}\rho_i-Q_{ij}\sigma_j\|_1.$$
--
--   The independent nonnegative arrays satisfy $\sum_jP_{ij}=p_i$ and $\sum_iQ_{ij}=q_j$. Their other marginals are free. This identifies the factor distance $D_*$ with EHS distance, rather than with single-array Kantorovich transport.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 22, Unnumbered equality of factor distance (53) and EHS (54)

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

/-- PDF pp.21–22, (53)–(54): factor distance equals the TWO-array EHS infimum. -/
theorem ehsFactorization {I : Type} [Countable I] [Nonempty I] (mu nu : CountableStateEnsemble I) :
    distanceStar mu nu = distanceEHS mu nu := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
