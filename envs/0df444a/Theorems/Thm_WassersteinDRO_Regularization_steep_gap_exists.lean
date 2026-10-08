-- Prove2me | Theorems.Thm_WassersteinDRO_Regularization_steep_gap_exists
-- name    : WassersteinDRO.Regularization.steep_gap_exists
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-05T08:56:17.284272+00:00
-- url     : https://prove2.me/theorems/f291dc12-a287-4da8-9b17-2b3fc309a12d
-- title:
--   Steep gap below the Lipschitz modulus: some pair has secant slope exceeding lam
-- statement:
--   If lam is strictly below the Lipschitz modulus of ℓ, some pair of distinct points has secant slope exceeding lam.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, INFORMS TutORials 2019 (Theorem 10, Lipschitz regularization of Wasserstein DRO); decomposition leaves of WassersteinDRO.Regularization.convex_loss_p1_borel (d58d7d19-a202-486d-8c9a-5855000c0837).

import Mathlib
import Definitions.Def_WassersteinDRO_Regularization_lipschitzModulus

namespace WassersteinDRO.Regularization

theorem steep_gap_exists {E : Type*} [NormedAddCommGroup E] (ℓ : E → ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) (hlt : ENNReal.ofReal lam < lipschitzModulus ℓ) :
    ∃ x y : E, x ≠ y ∧ lam * ‖x - y‖ < ℓ x - ℓ y := by sorry
end WassersteinDRO.Regularization
