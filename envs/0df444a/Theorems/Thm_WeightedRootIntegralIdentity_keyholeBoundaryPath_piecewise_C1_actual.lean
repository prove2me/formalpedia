-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_keyholeBoundaryPath_piecewise_C1_actual
-- name    : WeightedRootIntegralIdentity.keyholeBoundaryPath_piecewise_C1_actual
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-18T22:39:53.866418+00:00
-- url     : https://prove2.me/theorems/a054c8ff-ddf0-4748-84dd-2855675573be
-- title:
--   Piecewise C1 regularity of the assembled keyhole boundary path
-- statement:
--   The four smooth pieces of the assembled keyhole boundary path—the upper bank, outer arc, lower bank, and inner arc—are each continuously differentiable on the interiors of their parameter intervals.
-- source:
--   Direct differentiation of the affine bank parametrizations and circular-arc exponential parametrizations on each open quarter interval.

import Mathlib
import Definitions.Def_keyholeBoundaryPath
open scoped Interval

namespace WeightedRootIntegralIdentity

theorem keyholeBoundaryPath_piecewise_C1_actual
    (a₀ a₁ r R : ℝ) :
    ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo 0 (1 / 4)) ∧
    ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo (1 / 4) (1 / 2)) ∧
    ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo (1 / 2) (3 / 4)) ∧
    ContDiffOn ℝ 1 (keyholeBoundaryPath a₀ a₁ r R) (Set.Ioo (3 / 4) 1) := by sorry

end WeightedRootIntegralIdentity
