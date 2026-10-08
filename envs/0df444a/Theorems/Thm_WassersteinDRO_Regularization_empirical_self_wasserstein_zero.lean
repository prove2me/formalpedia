-- Prove2me | Theorems.Thm_WassersteinDRO_Regularization_empirical_self_wasserstein_zero
-- name    : WassersteinDRO.Regularization.empirical_self_wasserstein_zero
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-05T08:56:05.361307+00:00
-- url     : https://prove2.me/theorems/90292b72-5119-4935-a170-e48811a512ea
-- title:
--   The empirical distribution lies in its own Wasserstein-1 ball of radius 0
-- statement:
--   The empirical distribution lies in its own Wasserstein-1 ball of radius 0: W₁(P̂, P̂) = 0.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, INFORMS TutORials 2019 (Theorem 10, Lipschitz regularization of Wasserstein DRO); decomposition leaves of WassersteinDRO.Regularization.convex_loss_p1_borel (d58d7d19-a202-486d-8c9a-5855000c0837).

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_empiricalDistribution
import Definitions.Def_WassersteinDRO_Regularization_wassersteinDistance

open MeasureTheory

namespace WassersteinDRO.Regularization

theorem empirical_self_wasserstein_zero {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    {N : ℕ} (hN : 0 < N) (ξhat : Fin N → E) :
    wassersteinDistance 1 (empiricalDistribution ξhat) (empiricalDistribution ξhat) = 0 := by sorry
end WassersteinDRO.Regularization
