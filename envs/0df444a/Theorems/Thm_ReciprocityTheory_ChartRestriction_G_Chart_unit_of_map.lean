-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_unit_of_map
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.unit_of_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:37.465859+00:00
-- url     : https://prove2.me/theorems/97d4ef9e-2fbe-44fd-83d0-22f1a1817a74
-- title:
--   Chart: unit of map
-- statement:
--   The Chart construction uses the unit of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ScalePowMono.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ScalePowMono.lean#L35-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSCompScaleS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ScalePowMono
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

theorem ReciprocityTheory.ChartRestriction.G.Chart.unit_of_map {B B' : Type} [CommRing B] [Algebra S B] [CommRing B'] [Algebra S B'] [Algebra B B']
    [IsScalarTower S B B'] {u : S} (h : IsUnit (algebraMap S B u)) : IsUnit (algebraMap S B' u) := by sorry
