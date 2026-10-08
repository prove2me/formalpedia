-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_keyholePrimitivePaths_contDiff
-- name    : WeightedRootIntegralIdentity.keyholePrimitivePaths_contDiff
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-18T22:51:19.439491+00:00
-- url     : https://prove2.me/theorems/1156cf75-9050-4ad8-8354-a088d877a1a5
-- title:
--   Continuous differentiability of the four primitive keyhole path pieces
-- statement:
--   The affine upper and lower bank parametrizations and the exponential inner and outer circular-arc parametrizations are continuously differentiable on the real parameter line.
-- source:
--   Unfolding the affine bank maps and exponential circular-arc maps.

import Mathlib
import Definitions.Def_keyholeUpperBank
import Definitions.Def_keyholeLowerBank
import Definitions.Def_keyholeInnerArc
import Definitions.Def_keyholeOuterArc

namespace WeightedRootIntegralIdentity

theorem keyholePrimitivePaths_contDiff
    (a₀ a₁ r R : ℝ) :
    ContDiff ℝ 1 (fun t : ℝ => keyholeUpperBank (a₀ + 4 * t * (a₁ - a₀))) ∧
    ContDiff ℝ 1 (fun t : ℝ => keyholeLowerBank (a₁ + (4 * t - 2) * (a₀ - a₁))) ∧
    ContDiff ℝ 1 (fun t : ℝ => keyholeOuterArc R (4 * t - 1)) ∧
    ContDiff ℝ 1 (fun t : ℝ => keyholeInnerArc r (4 * t - 3)) := by sorry

end WeightedRootIntegralIdentity
