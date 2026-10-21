-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_equalProbabilityBound
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.equalProbabilityBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:00:16.208225+00:00
-- url     : https://prove2.me/theorems/cbe668c8-1ed6-4a8e-aba5-2a338f1e6044
-- title:
--   Unnumbered equal-probability specialization (64)
-- statement:
--   Let $\mu=\{p_i,\rho_i\}$ and $\nu=\{p_i,\sigma_i\}$ have the same probabilities and at most $m\ge1$ labels. Set $\varepsilon=\frac12\sum_i p_i\|\rho_i-\sigma_i\|_1$. Both Holevo quantities are finite and
--
--   $$|\chi(\mu)-\chi(\nu)|\le\varepsilon\log m+g(\varepsilon).$$
--
--   The right side can also use any nonnegative upper bound $t$ on all corresponding signal trace distances, including their maximum. This retains the average-distance specialization of (64).
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 26, Unnumbered equal-probability specialization (64)

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

/-- PDF p.26, (64): equal probabilities, average signal distance, and the
optional maximum-signal-distance replacement. Finiteness is concluded first. -/
theorem equalProbabilityBound {I : Type} [Countable I] [Nonempty I]
    (mu nu : CountableStateEnsemble I) (m : ℕ) (hm : 0 < m)
    (hmu : AtMostLabels m mu) (hnu : AtMostLabels m nu) (hw : mu.weight = nu.weight) :
    let epsilon := (∑' i, mu.weight i * extendedHalfTraceDistance (mu.state i).coefficients
      (nu.state i).coefficients).toReal
    countableHolevo mu < ⊤ ∧ countableHolevo nu < ⊤ ∧
    |(countableHolevo mu).toReal - (countableHolevo nu).toReal| ≤ epsilon * Real.log m + g epsilon ∧
    (∀ t : ℝ, 0 ≤ t →
      (∀ i < m, extendedHalfTraceDistance (mu.state i).coefficients (nu.state i).coefficients ≤ ENNReal.ofReal t) →
      |(countableHolevo mu).toReal - (countableHolevo nu).toReal| ≤ t * Real.log m + g t) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
