-- Prove2me | Theorems.Thm_WassersteinDRO_Regularization_convex_ray_slope_mono
-- name    : WassersteinDRO.Regularization.convex_ray_slope_mono
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-05T08:56:15.094716+00:00
-- url     : https://prove2.me/theorems/f3c4fb51-9d0c-4dbb-86ec-731e11a0832a
-- title:
--   Secant slopes along a ray are monotone for convex loss
-- statement:
--   For convex ℓ, secant slopes along a ray are monotone: the slope from y to y + t•u (unit direction u) grows with t.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, INFORMS TutORials 2019 (Theorem 10, Lipschitz regularization of Wasserstein DRO); decomposition leaves of WassersteinDRO.Regularization.convex_loss_p1_borel (d58d7d19-a202-486d-8c9a-5855000c0837).

import Mathlib

namespace WassersteinDRO.Regularization

theorem convex_ray_slope_mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : E → ℝ) (hconv : ConvexOn ℝ Set.univ ℓ)
    (y u : E) (hu : ‖u‖ = 1) (d t : ℝ) (hd : 0 < d) (hdt : d ≤ t) :
    (ℓ (y + d • u) - ℓ y) / d ≤ (ℓ (y + t • u) - ℓ y) / t := by sorry
end WassersteinDRO.Regularization
