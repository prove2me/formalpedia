-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_beamSplitter_heat_compatibility
-- name    : QAlgorithms.Papers.Independent.Next46.P17.beamSplitter_heat_compatibility
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:22:34.824875+00:00
-- url     : https://prove2.me/theorems/fa5e0408-3db9-4f77-bf76-cb79f6789248
-- title:
--   Lemma III.2: beamSplitter heat compatibility
-- statement:
--   Let $n\geq1$, $t_X,t_Y\geq0$, and $0<\lambda<1$. Let $\mathcal N_t$ be the canonical Gaussian displacement channel on the full $n$-mode trace class, with $\mathcal N_0=\mathrm{id}$ and displacement variance $t/2$ per quadrature. Let $\mathcal E_\lambda$ be the beam-splitter channel (45). Then
--
--   $$
--   \mathcal E_\lambda\circ(\mathcal N_{t_X}\otimes\mathcal N_{t_Y})
--   =\mathcal N_{\lambda t_X+(1-\lambda)t_Y}\circ\mathcal E_\lambda.
--   $$
--
--   This equality holds on all trace-class inputs, including correlated densities. It is not restricted to Gaussian states or product inputs.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 8, Lemma III.2, (56)

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

/-- PDF p.8, Lemma III.2, (56): full channel equality, with independent times
and no Gaussian, product-input, moment or differentiability restriction. -/
theorem beamSplitter_heat_compatibility {n : ℕ} (hn : 0 < n)
    (tX tY lam : ℝ) (htX : 0 ≤ tX) (htY : 0 ≤ tY)
    (hlam : 0 < lam) (hlamOne : lam < 1)
    (X : Matrix (FockIndex n × FockIndex n) (FockIndex n × FockIndex n) ℂ)
    (hX : IsTraceClass X) :
    beamSplitter lam (independentHeat tX tY X) =
      diffusionChannel (lam * tX + (1 - lam) * tY) (beamSplitter lam X) := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
