-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scale_pow_add
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.scale_pow_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:32:27.129892+00:00
-- url     : https://prove2.me/theorems/b35e2c3b-127e-5cbd-a182-0c273b66b334
-- title:
--   Chart: scale pow add
-- statement:
--   The Chart construction uses the scale pow add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ScalePowMono.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/ScalePowMono.lean#L46-L48

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
variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem ReciprocityTheory.ChartRestriction.G.Chart.scale_pow_add {A : Type} [CommRing A] [Algebra S A] (x : A) (a b : ℕ) (y : sp (R₀ := S) (DualNumber A) ⟶ G) :
    spMap (scaleS (S := S) (x ^ a)) ≫ spMap (scaleS (x ^ b)) ≫ y = spMap (scaleS (x ^ (a + b))) ≫ y := by sorry
