-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_toAlgHom_restrict
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.toAlgHom_restrict
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:23:37.513721+00:00
-- url     : https://prove2.me/theorems/8c5a7034-5aff-4dd3-a759-881dda1692c2
-- title:
--   Chart: to Alg Hom restrict
-- statement:
--   The Chart construction uses the to Alg Hom restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/DualMapSCompScaleS.lean#L14-L17

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.toAlgHom_restrict {S : Type} [CommRing S] (R : Type) [CommRing R] [Algebra S R] (A A' : Type) [CommRing A]
    [Algebra S A] [Algebra R A] [IsScalarTower S R A] [CommRing A'] [Algebra S A'] [Algebra R A'] [IsScalarTower S R A']
    [Algebra A A'] [IsScalarTower R A A'] [IsScalarTower S A A'] :
    (IsScalarTower.toAlgHom R A A').restrictScalars S = IsScalarTower.toAlgHom S A A' := by sorry
