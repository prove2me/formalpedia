-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_maDensity_congr_of_eventuallyEq
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.maDensity_congr_of_eventuallyEq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:37.925378+00:00
-- url     : https://prove2.me/theorems/a39c6e78-ec20-4a6e-a22a-e71aabd9e125
-- title:
--   Geo: ma Density congr of eventually Eq
-- statement:
--   The Geo construction uses the ma Density congr of eventually Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFS.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterFS.lean#L11-L20

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFS
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
open MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem ReciprocityTheory.ChartRestriction.G.Geo.maDensity_congr_of_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ j, φ j =ᶠ[𝓝 y] ψ j) : maDensity φ y = maDensity ψ y := by sorry
