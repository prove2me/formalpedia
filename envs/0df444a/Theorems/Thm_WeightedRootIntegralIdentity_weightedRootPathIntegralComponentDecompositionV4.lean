-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weightedRootPathIntegralComponentDecompositionV4
-- name    : WeightedRootIntegralIdentity.weightedRootPathIntegralComponentDecompositionV4
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T04:48:42.979787+00:00
-- url     : https://prove2.me/theorems/3efa6911-3b47-486e-a9c6-503f94d12875
-- title:
--   Connect path integral to four contour component integrals
-- statement:
--   If the assembled path integral P agrees with the keyhole boundary integral, then it equals the oriented sum of the upper and lower banks, both vertical sides, and the inner and outer arcs.
-- source:
--   by rw [hpath, hdecomp]

import Mathlib
import Definitions.Def_weightedRootFiniteContourComponentsV2
open scoped BigOperators Interval
namespace WeightedRootIntegralIdentity
theorem weightedRootPathIntegralComponentDecompositionV4
    (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ r R : ℝ) (P : ℂ)
    (hpath : P = weightedRootBoundaryIntegral n a w a₀ a₁ r R)
    (hdecomp : weightedRootBoundaryIntegral n a w a₀ a₁ r R =
      weightedRootFiniteUpperBankIntegral n a w a₀ a₁ r +
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ r +
      weightedRootRightVerticalIntegral n a w a₁ r R +
      weightedRootLeftVerticalIntegral n a w a₀ r R +
      weightedRootFiniteInnerArcIntegral n a w r +
      weightedRootFiniteOuterArcIntegral n a w R) :
    P = weightedRootFiniteUpperBankIntegral n a w a₀ a₁ r +
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ r +
      weightedRootRightVerticalIntegral n a w a₁ r R +
      weightedRootLeftVerticalIntegral n a w a₀ r R +
      weightedRootFiniteInnerArcIntegral n a w r +
      weightedRootFiniteOuterArcIntegral n a w R := by sorry
end WeightedRootIntegralIdentity
