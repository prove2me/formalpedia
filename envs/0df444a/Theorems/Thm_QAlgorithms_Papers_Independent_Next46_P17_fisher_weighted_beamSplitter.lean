-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_fisher_weighted_beamSplitter
-- name    : QAlgorithms.Papers.Independent.Next46.P17.fisher_weighted_beamSplitter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:28:28.928975+00:00
-- url     : https://prove2.me/theorems/074ebf5b-ff06-40e5-82e9-36b47575f7b6
-- title:
--   Theorem VI.2: fisher weighted beamSplitter
-- statement:
--   Let $n\geq1$, $0<\lambda<1$, and let $\rho_X,\rho_Y$ be normalized full $n$-mode states. For each state under consideration, assume all its displacement-direction relative entropies are locally finite and twice differentiable at zero. Let $J$ be the unaveraged sum of these $2n$ derivatives, using natural logarithms. For real $w_X,w_Y$ and $w=\sqrt\lambda\,w_X+\sqrt{1-\lambda}\,w_Y$,
--
--   $$
--   w^2J(\mathcal E_\lambda(\rho_X\otimes\rho_Y))\leq w_X^2J(\rho_X)+w_Y^2J(\rho_Y).
--   $$
--
--   The cancellation case $w=0$ is included. This source concerns the physical beam splitter.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 11, Theorem VI.2, pp.11–12

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

/-- PDF pp.11–12, Theorem VI.2: weighted total Fisher inequality.
The sum is over 2n directions without averaging; cancellation w=0 is allowed. -/
theorem fisher_weighted_beamSplitter {n : ℕ} (hn : 0 < n)
    (lam wX wY : ℝ) (hlam : 0 < lam) (hlamOne : lam < 1)
    (rhoX rhoY : State (FockIndex n))
    (hX : TotalFisherRegular rhoX.coefficients) (hY : TotalFisherRegular rhoY.coefficients)
    (hOut : TotalFisherRegular (beamSplitter lam
      (productCoeff rhoX.coefficients rhoY.coefficients))) :
    (Real.sqrt lam * wX + Real.sqrt (1 - lam) * wY) ^ 2 *
      totalFisher (beamSplitter lam (productCoeff rhoX.coefficients rhoY.coefficients)) ≤
    wX ^ 2 * totalFisher rhoX.coefficients + wY ^ 2 * totalFisher rhoY.coefficients := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
