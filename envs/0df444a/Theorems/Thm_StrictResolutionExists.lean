-- Prove2me | Theorems.Thm_StrictResolutionExists
-- name    : StrictResolutionExists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:25.010665+00:00
-- url     : https://prove2.me/theorems/1ad8797b-30bd-487b-add9-ee3f3ba5d0d3
-- title:
--   Strict Resolution Exists: Strict Resolution Exists
-- statement:
--   Every piecewise-geodesic curve of positive length admits a strictly increasing (non-degenerate)
--   resolution into geodesic edges.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/StrictResolutionExists.lean#L11-L33
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/StrictResolutionExists.lean#L11-L33

import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_MinimizingResolutionStrict
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_StrictResolutionExists
import Theorems.Thm_MinimizingResolutionStrict

set_option autoImplicit false
open Set

theorem StrictResolutionExists {E : Type*} [MetricSpace E] (γ : Curve E)
    (hpg : IsPiecewiseGeodesic γ) (hlen : 0 < γ.len) :
    ∃ k : ℕ, 0 < k ∧ ∃ s : ℕ → ℝ, IsGeodesicResolution γ k s ∧ ∀ i < k, s i < s (i + 1) := by sorry
