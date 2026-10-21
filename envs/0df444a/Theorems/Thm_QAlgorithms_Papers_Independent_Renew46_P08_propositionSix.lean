-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_propositionSix
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.propositionSix
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:01:09.974667+00:00
-- url     : https://prove2.me/theorems/6c3459c8-34ac-4e2c-b9f0-6a3d90c42c41
-- title:
--   Proposition 6, (65)–(66): local discrete continuity
-- statement:
--   Let $\mu_n$ be countable ensembles and $\mu_0$ a countable ensemble. Either of the following conditions suffices: (A) $D_*(\mu_n,\mu_0)\to0$ and $H(\overline\rho_n)\to H(\overline\rho_0)<\infty$; (B) $D_0(\mu_n,\mu_0)\to0$ and $S(p^n)\to S(p^0)<\infty$, where $S$ is Shannon entropy in nats. In each case,
--
--   $$\chi(\mu_n)\longrightarrow\chi(\mu_0)<\infty.$$
--
--   All averages are constructed from their ensembles. No continuity of individual signal entropies is assumed, and convergence before the limit uses extended entropy values.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 26, Proposition 6, (65)–(66): local discrete continuity

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

/-- Proposition 6, PDF pp.26–27, (65)–(66): two DIFFERENT convergence criteria.
Only the limiting countableAverage or Shannon entropy must be finite; all limits retain
extended values, so early infinite terms cannot be converted silently to zero. -/
theorem propositionSix {I : Type} [Countable I] [Nonempty I]
    (mu : ℕ → CountableStateEnsemble I) (mu0 : CountableStateEnsemble I) :
    ((Tendsto (fun n => distanceStar (mu n) mu0) atTop (nhds 0) ∧
      Tendsto (fun n => extendedEntropyNats (countableAverage (mu n))) atTop
        (nhds (extendedEntropyNats (countableAverage mu0))) ∧ extendedEntropyNats (countableAverage mu0) < ⊤) →
      Tendsto (fun n => countableHolevo (mu n)) atTop (nhds (countableHolevo mu0)) ∧ countableHolevo mu0 < ⊤) ∧
    ((Tendsto (fun n => distance0 (mu n) mu0) atTop (nhds 0) ∧
      Tendsto (fun n => countableShannonNats (mu n).weight) atTop (nhds (countableShannonNats mu0.weight)) ∧
        countableShannonNats mu0.weight < ⊤) →
      Tendsto (fun n => countableHolevo (mu n)) atTop (nhds (countableHolevo mu0)) ∧ countableHolevo mu0 < ⊤) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
