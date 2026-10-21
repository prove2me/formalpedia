-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_fisher_convexity_beamSplitter
-- name    : QAlgorithms.Papers.Independent.Next46.P17.fisher_convexity_beamSplitter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:29:00.779843+00:00
-- url     : https://prove2.me/theorems/cfbf365c-4692-4b26-aa19-24476dfe46da
-- title:
--   Corollary VI.3: fisher convexity beamSplitter
-- statement:
--   Let $n\geq1$, $0<\lambda<1$, and let $\rho_X,\rho_Y$ be normalized $n$-mode states on the full Hilbert space. Assume the locally finite, genuine twice-differentiability domain for every quadrature-displacement divergence of the inputs and output. Let $J$ be their unaveraged $2n$-direction Fisher sum. Then
--
--   $$
--   J(\mathcal E_\lambda(\rho_X\otimes\rho_Y))\leq\lambda J(\rho_X)+(1-\lambda)J(\rho_Y).
--   $$
--
--   This is Fisher convexity under physical beam-splitter mixing of independent states.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 12, Corollary VI.3, (85)

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

/-- PDF p.12, Corollary VI.3, (85): Fisher convexity under physical mixing. -/
theorem fisher_convexity_beamSplitter {n : ℕ} (hn : 0 < n)
    (lam : ℝ) (hlam : 0 < lam) (hlamOne : lam < 1)
    (rhoX rhoY : State (FockIndex n))
    (hX : TotalFisherRegular rhoX.coefficients) (hY : TotalFisherRegular rhoY.coefficients)
    (hOut : TotalFisherRegular (beamSplitter lam
      (productCoeff rhoX.coefficients rhoY.coefficients))) :
    totalFisher (beamSplitter lam (productCoeff rhoX.coefficients rhoY.coefficients)) ≤
    lam * totalFisher rhoX.coefficients + (1 - lam) * totalFisher rhoY.coefficients := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
