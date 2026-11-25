-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff_tanS
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff_tanS
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:41:52.37164+00:00
-- url     : https://prove2.me/theorems/e3f07311-41ec-5856-8c1b-d20a22e60f0b
-- title:
--   Chart: is Tan iff tan S
-- statement:
--   The Chart construction uses the is Tan iff tan S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PushRProdPtsResP.lean#L55-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PushRProdPtsResP.lean#L55-L66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullbackFactor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushRProdPtsResP
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
variable (p : Ideal S) [p.IsPrime]

theorem ReciprocityTheory.ChartRestriction.G.Chart.isTan_iff_tanS (w : sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p)) ⟶ Gp (G := G) p) :
    IsTan w ↔ TanS (pushR G w) := by sorry
