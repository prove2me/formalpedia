-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_orderedEnsembleConvergence
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.orderedEnsembleConvergence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:55:03.369759+00:00
-- url     : https://prove2.me/theorems/f7bed33b-3312-4743-9be8-ef5581a09c29
-- title:
--   Unnumbered D0 convergence equivalence (52)
-- statement:
--   Let $\mu_n=\{p_i^n,\rho_i^n\}$ and $\mu_0=\{p_i^0,\rho_i^0\}$ be countable labeled ensembles, allowing repetitions and zero weights. For $D_0(\mu,\nu)=\frac12\sum_i\|p_i\rho_i-q_i\sigma_i\|_1$,
--
--   $$D_0(\mu_n,\mu_0)\to0\quad\Longleftrightarrow\quad p_i^n\to p_i^0\ (\forall i),\quad \rho_i^n\to\rho_i^0\ (\forall i:p_i^0\ne0).$$
--
--   State convergence is in trace norm. Zero-limit-weight labels impose no signal convergence condition. On raw presentations this distance is a pseudometric.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 21, Unnumbered D0 convergence equivalence (52)

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

/-- PDF pp.20–21, (52): no convergence is imposed at labels of zero LIMIT weight. -/
theorem orderedEnsembleConvergence {I : Type} [Countable I] [Nonempty I]
    (mu : ℕ → CountableStateEnsemble I) (mu0 : CountableStateEnsemble I) :
    Tendsto (fun n => distance0 (mu n) mu0) atTop (nhds 0) ↔
      (∀ i, Tendsto (fun n => (mu n).weight i) atTop (nhds (mu0.weight i))) ∧
      (∀ i, mu0.weight i ≠ 0 →
        Tendsto (fun n => (mu n).state i) atTop (nhds (mu0.state i))) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
