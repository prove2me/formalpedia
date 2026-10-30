-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_holevo_minimum_output
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.holevo_minimum_output
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:03:17.303823+00:00
-- url     : https://prove2.me/theorems/65bb1903-c519-4f0c-8626-cbee7e742a65
-- title:
--   Unnumbered general Holevo/minimum-output bound (7.10)
-- statement:
--   Let $\mathcal E$ be a CPTP map from an $e$-dimensional input to a $d$-dimensional output, where $e,d\ge1$. Let $H$ be von Neumann entropy in nats, including singular states. Define $H_{\min}(\mathcal E)=\min_\rho H(\mathcal E(\rho))$ over all normalized density inputs, and define the single-use Holevo quantity by
--   $$\chi(\mathcal E)=\sup_{\{p_i,\rho_i\}}\left[H\left(\sum_i p_i\mathcal E(\rho_i)\right)-\sum_i p_iH(\mathcal E(\rho_i))\right],$$
--   where arbitrary finite ensembles use nonnegative weights summing to one and normalized states. The ensemble supremum is attained, so it is also the maximum in (7.9). The minimum output entropy is attained, and
--   $$\chi(\mathcal E)\le\log d-H_{\min}(\mathcal E).$$
--   This bounds the single-use Holevo quantity; no regularized entangled-input capacity is substituted.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 27, Unnumbered general Holevo/minimum-output bound (7.10)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF p.27, (7.10): single-use Holevo bound for any finite positive-dimensional CPTP map.
The output minimum and the ensemble maximum are attained; no regularized capacity is substituted. -/
theorem holevo_minimum_output {e d : ℕ} (he : 0 < e) (hd : 0 < d)
    (N : Superop (Fin e) (Fin d)) (hN : IsChannel N) :
    holevoNats N ≤ Real.log (d : ℝ) - finiteMinimumOutputEntropyNats N ∧
    (∃ rho : Mat e, IsDensityMatrix rho ∧
      entropy (N rho) = finiteMinimumOutputEntropyNats N) ∧
    ∃ ens : Ensemble (Fin e), holevoNats N = Real.log 2 *
      QAlgorithms.Papers.Independent.Information100.P08.outputHolevo N ens := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
