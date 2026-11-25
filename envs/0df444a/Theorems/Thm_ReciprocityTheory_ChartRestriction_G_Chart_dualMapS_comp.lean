-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dualMapS_comp
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.dualMapS_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:08:06.538804+00:00
-- url     : https://prove2.me/theorems/a616b42b-a8c9-46d3-95f8-90105d1dc151
-- title:
--   Chart: dual Map S comp
-- statement:
--   The Chart construction uses the dual Map S comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L88-L92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
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
variable {S : Type} [CommRing S]

theorem ReciprocityTheory.ChartRestriction.G.Chart.dualMapS_comp {A A' A'' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] [CommRing A'']
    [Algebra S A''] (j : A →ₐ[S] A') (j' : A' →ₐ[S] A'') : (dualMapS j').comp (dualMapS j) = dualMapS (j'.comp j) := by sorry
