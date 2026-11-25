-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_abs_det_restrictScalars
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.abs_det_restrictScalars
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:23:12.533194+00:00
-- url     : https://prove2.me/theorems/3dfc11b7-1b67-42b9-bb38-5c652ca300d2
-- title:
--   Geo: abs det restrict Scalars
-- statement:
--   The Geo construction uses the abs det restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeG.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeG.lean#L18-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Set Filter Topology Function
variable {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.abs_det_restrictScalars (f : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
    |(f.restrictScalars ℝ).det| = ‖LinearMap.det (f : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2 := by sorry
