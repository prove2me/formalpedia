-- Prove2me | Theorems.Thm_PHarmJetEquicontinuity
-- name    : PHarmJetEquicontinuity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:19:18.364142+00:00
-- url     : https://prove2.me/theorems/7092af36-68a1-4809-a964-607951f62779
-- title:
--   PHarm Jet Equicontinuity: PHarm Jet Equicontinuity
-- statement:
--   Transport of the uniform first-order estimate to an arbitrary ball.  If `v` is
--   `p`-harmonic on `ball x₀ (2 * R)` and bounded there by `M`, then on the smaller ball
--   `ball x₀ (3 * R / 2)` the function `v` is `C^1`, its classical gradient is bounded by
--   `F.C₀ * M / (2 * R)`, and that gradient is `F.kappa`-Holder with constant
--   `F.C₀ * M / (2 * R)` measured in the rescaled variable.
--
--   Both bounds are uniform over the family of all such `v`, which is what an
--   Arzela-Ascoli argument consumes.  Factoring the TRANSPORT rather than the
--   Arzela-Ascoli application matters because the two consumers apply compactness on
--   different bases but need this identical statement.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmJetEquicontinuity.lean#L14-L132
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PHarmJetEquicontinuity.lean#L14-L132

import Definitions.Def_PHigherOrder_PHarmNormalize
import Definitions.Def_PHigherOrder_FirstOrderEstimateInput
import Definitions.Def_PHigherOrder_PHarmJetEquicontinuity
import Theorems.Thm_PHarmNormalize

set_option autoImplicit false

theorem PHarmJetEquicontinuity (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (F : FirstOrderEstimateInput p) (x₀ : Plane) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (v : Plane → ℝ) (g : Plane → Plane)
    (hv : IsPHarm p (Metric.ball x₀ (2 * R)) v g)
    (hbd : ∀ z ∈ Metric.ball x₀ (2 * R), |v z| ≤ M) :
    ContDiffOn ℝ 1 v (Metric.ball x₀ (3 * R / 2)) ∧
    (∀ z ∈ Metric.ball x₀ (3 * R / 2), ‖gradient v z‖ ≤ F.C₀ * M / (2 * R)) ∧
    (∀ z ∈ Metric.ball x₀ (3 * R / 2), ∀ z' ∈ Metric.ball x₀ (3 * R / 2),
      ‖gradient v z - gradient v z'‖
        ≤ F.C₀ * M / (2 * R) * (‖z - z'‖ / (2 * R)) ^ F.kappa) := by sorry
