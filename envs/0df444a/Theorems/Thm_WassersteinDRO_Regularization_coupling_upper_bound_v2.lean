-- Prove2me | Theorems.Thm_WassersteinDRO_Regularization_coupling_upper_bound_v2
-- name    : WassersteinDRO.Regularization.coupling_upper_bound_v2
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-06T16:46:33.097465+00:00
-- url     : https://prove2.me/theorems/20ff2b51-23fe-4524-b32b-79f67a5c5c0c
-- title:
--   Risk gap bounded by Lipschitz modulus times Wasserstein-1 distance
-- statement:
--   For measurable ℓ integrable under both Q and the empirical P̂, the risk gap E_Q[ℓ] − E_P̂[ℓ] is at most Lip(ℓ)·W₁(Q,P̂). (This version adds the hypothesis `0 < N`; the previous statement was disproved at `N = 0`, where the empirical distribution is the zero measure.)
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, INFORMS TutORials 2019 (Theorem 10, Lipschitz regularization of Wasserstein DRO); decomposition leaves of WassersteinDRO.Regularization.convex_loss_p1_borel (d58d7d19-a202-486d-8c9a-5855000c0837).

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_WassersteinDRO_Regularization_nominalRisk
import Definitions.Def_WassersteinDRO_Regularization_lipschitzModulus
import Definitions.Def_WassersteinDRO_Regularization_wassersteinDistance

open MeasureTheory

namespace WassersteinDRO.Regularization

theorem coupling_upper_bound_v2 {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [BorelSpace E] {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) (ℓ : E → ℝ) (hm : Measurable ℓ)
    (Q : Measure E) [IsProbabilityMeasure Q]
    (hQ : Integrable ℓ Q) (hP : Integrable ℓ (empiricalDistribution ξhat)) :
    ENNReal.ofReal (nominalRisk Q ℓ - nominalRisk (empiricalDistribution ξhat) ℓ) ≤
      lipschitzModulus ℓ * wassersteinDistance 1 Q (empiricalDistribution ξhat) := by sorry
end WassersteinDRO.Regularization
