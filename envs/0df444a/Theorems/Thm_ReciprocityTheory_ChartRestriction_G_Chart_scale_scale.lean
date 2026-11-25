-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scale_scale
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.scale_scale
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:07:28.53551+00:00
-- url     : https://prove2.me/theorems/33527729-2b36-43b2-a111-d7e5ba8390e0
-- title:
--   Chart: scale scale
-- statement:
--   The Chart construction uses the scale scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L104-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L104-L106

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
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
variable {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem ReciprocityTheory.ChartRestriction.G.Chart.scale_scale {A : Type} [CommRing A] [Algebra S A] (a b : A) (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (scaleS (S := S) a) ≫ spMap (scaleS b) ≫ y = spMap (scaleS (a * b)) ≫ y := by sorry
