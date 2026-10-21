-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P17_fisher_directional_beamSplitter
-- name    : QAlgorithms.Papers.Independent.Next46.P17.fisher_directional_beamSplitter
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:27:37.294404+00:00
-- url     : https://prove2.me/theorems/8d3fdb04-da31-442f-9567-f612968235a5
-- title:
--   Theorem VI.2 proof: fisher directional beamSplitter
-- statement:
--   Let $n\geq1$, $0<\lambda<1$, and let $\rho_X,\rho_Y$ be normalized full $n$-mode states. Fix a quadrature $R$, real weights $w_X,w_Y$, and set $w=\sqrt\lambda\,w_X+\sqrt{1-\lambda}\,w_Y$. For a density $\sigma$, write $J_R(\sigma)$ for the actual second derivative at zero of $D(\sigma\Vert D_R(\theta)\sigma D_R(\theta)^\dagger)$, with natural logarithms. Assume these divergences are locally finite and twice differentiable for both inputs and the output. Then
--
--   $$
--   w^2J_R(\mathcal E_\lambda(\rho_X\otimes\rho_Y))\leq w_X^2J_R(\rho_X)+w_Y^2J_R(\rho_Y).
--   $$
--
--   This retains the directional inequality before summation. The unscaled directional Fisher information is used on each side.
-- source:
--   The entropy power inequality for quantum systems, arXiv:1205.3409v2, PDF p. 11, Theorem VI.2 proof, pp.11–12

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

/-- PDF pp.11–12, Theorem VI.2 proof: the directional weighted inequality.
The unscaled J_R occurs on each side; the extra w in the p.12 family label
is corrected as uniquely determined by the p.11 data-processing display. -/
theorem fisher_directional_beamSplitter {n : ℕ} (hn : 0 < n)
    (lam wX wY : ℝ) (hlam : 0 < lam) (hlamOne : lam < 1)
    (R : Fin n × Fin 2) (rhoX rhoY : State (FockIndex n))
    (hX : FisherRegular (directionOrbit R rhoX.coefficients) 0)
    (hY : FisherRegular (directionOrbit R rhoY.coefficients) 0)
    (hOut : FisherRegular (directionOrbit R (beamSplitter lam
      (productCoeff rhoX.coefficients rhoY.coefficients))) 0) :
    (Real.sqrt lam * wX + Real.sqrt (1 - lam) * wY) ^ 2 *
      fisher (directionOrbit R (beamSplitter lam
        (productCoeff rhoX.coefficients rhoY.coefficients))) 0 ≤
    wX ^ 2 * fisher (directionOrbit R rhoX.coefficients) 0 +
      wY ^ 2 * fisher (directionOrbit R rhoY.coefficients) 0 := by sorry

end QAlgorithms.Papers.Independent.Next46.P17

end
