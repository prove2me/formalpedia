-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_corollaryFive
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.corollaryFive
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:02:34.744618+00:00
-- url     : https://prove2.me/theorems/963d1c5d-f1dc-40bc-9321-22332297041e
-- title:
--   Corollary 5, (67): stability under signal perturbations
-- statement:
--   Fix a countable probability law $p$ with finite Shannon entropy $S(p)$. If $\rho_i^n\to\rho_i^0$ in trace norm for each label $i$, then
--
--   $$\chi(\{p_i,\rho_i^n\})\longrightarrow\chi(\{p_i,\rho_i^0\})\le S(p).$$
--
--   No uniformity in $i$ and no convergence of the signal entropies are required. The assertion describes stability under perturbations of the signals of a fixed finite-Shannon ensemble.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 27, Corollary 5, (67): stability under signal perturbations

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

/-- Corollary 5, PDF p.27, (67): pointwise signal convergence at fixed finite-
Shannon weights; neither uniform convergence nor signal-entropy convergence. -/
theorem corollaryFive {I : Type} [Countable I] [Nonempty I]
    (mu : ℕ → CountableStateEnsemble I) (mu0 : CountableStateEnsemble I)
    (hw : ∀ n, (mu n).weight = mu0.weight) (hS : countableShannonNats mu0.weight < ⊤)
    (hs : ∀ i, Tendsto (fun n => (mu n).state i) atTop (nhds (mu0.state i))) :
    Tendsto (fun n => countableHolevo (mu n)) atTop (nhds (countableHolevo mu0)) ∧ countableHolevo mu0 ≤ countableShannonNats mu0.weight := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
