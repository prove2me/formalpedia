-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dAway_ext
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.dAway_ext
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:03:39.245882+00:00
-- url     : https://prove2.me/theorems/da1be9cc-fa4a-4392-9e91-7bd6d5b2c22d
-- title:
--   Chart: d Away ext
-- statement:
--   The Chart construction uses the d Away ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSOfIdToRingHom.lean#L30-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSOfIdToRingHom.lean#L30-L46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] (s : S)

theorem ReciprocityTheory.ChartRestriction.G.Chart.dAway_ext {T : Type} [CommRing T] {χ₁ χ₂ : DualNumber (Localization.Away s) →+* T}
    (h : χ₁.comp (dAway s) = χ₂.comp (dAway s)) : χ₁ = χ₂ := by sorry
