-- Prove2me | Theorems.Thm_WassersteinDRO_Regularization_empirical_risk_computation
-- name    : WassersteinDRO.Regularization.empirical_risk_computation
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-05T08:56:00.83711+00:00
-- url     : https://prove2.me/theorems/cf1e0af8-f44c-4b32-851b-a1da27d3fd34
-- title:
--   Empirical risk computation: nominal risk under the empirical distribution is the sample average
-- statement:
--   The nominal risk of a measurable loss under the empirical distribution of N samples equals the sample average of the loss.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, INFORMS TutORials 2019 (Theorem 10, Lipschitz regularization of Wasserstein DRO); decomposition leaves of WassersteinDRO.Regularization.convex_loss_p1_borel (d58d7d19-a202-486d-8c9a-5855000c0837).

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_WassersteinDRO_Regularization_nominalRisk

open MeasureTheory

namespace WassersteinDRO.Regularization

theorem empirical_risk_computation {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) (ℓ : E → ℝ) (hm : Measurable ℓ) :
    nominalRisk (empiricalDistribution ξhat) ℓ =
      (1 / (N : ℝ)) * Finset.sum Finset.univ (fun i => ℓ (ξhat i)) := by sorry
end WassersteinDRO.Regularization
