-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_heat_entropy_asymptotics
-- name    : QAlgorithms.Papers.Independent.Next46.P17.heat_entropy_asymptotics
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:23:24.707123+00:00
-- url     : https://prove2.me/theorems/0a200fe6-0766-4f2f-8f3a-3398e0727bd2
-- title:
--   Corollary III.4: heat entropy asymptotics
-- statement:
--   Let $n\geq1$ and let $\rho$ be a normalized $n$-mode state with finite first and second quadrature moments, equivalently finite mean total photon number. Let $\mathcal N_t$ be canonical diffusion and let $S$ denote entropy in nats. There are constants $C,T>0$, depending on the initial state, such that for every $t\geq T$ the output entropy is finite and
--
--   $$
--   \left|\frac{S(\mathcal N_t\rho)}n-(1-\log2+\log t)\right|\leq\frac Ct,
--   \qquad
--   \left|\frac{e^{S(\mathcal N_t\rho)/n}}t-\frac e2\right|\leq\frac Ct.
--   $$
--
--   The leading entropy-growth terms do not depend on the initial state. The second estimate concerns entropy power divided by time.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 9, Corollary III.4

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17

noncomputable section

open Filter MeasureTheory

open scoped ENNReal BigOperators Topology

namespace QAlgorithms.Papers.Independent.Next46.P17

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19 (productWeyl FiniteMeanEnergy PhysicalCovariance Cov FockIndex covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

/-- PDF p.9, Corollary III.4: both absolute-value estimates, including the
1/t normalization in the entropy-power estimate. The finite-moment standing
domain is the equivalent finite mean number energy. Constants follow the state. -/
theorem heat_entropy_asymptotics {n : ℕ} (hn : 0 < n)
    (rho : State (FockIndex n)) (hEnergy : FiniteMeanEnergy rho.coefficients) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, T ≤ t →
      extendedEntropyNats (diffusionChannel t rho.coefficients) ≠ ⊤ ∧
      |(extendedEntropyNats (diffusionChannel t rho.coefficients)).toReal / (n : ℝ) -
        (1 - Real.log 2 + Real.log t)| ≤ C / t ∧
      |(bosonicEntropyPower n (extendedEntropyNats (diffusionChannel t rho.coefficients))).toReal / t -
        Real.exp 1 / 2| ≤ C / t := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
