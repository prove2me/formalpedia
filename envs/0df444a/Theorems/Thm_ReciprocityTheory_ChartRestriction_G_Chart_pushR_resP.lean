-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_resP
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.pushR_resP
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:41:34.87662+00:00
-- url     : https://prove2.me/theorems/ca1a5b70-634d-437e-b938-914b2b60ba8d
-- title:
--   Chart: push R res P
-- statement:
--   The Chart construction uses the push R res P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PushRProdPtsResP.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PushRProdPtsResP.lean#L35-L38

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.pushR_resP (v : sp (R₀ := S) (DualNumber S) ⟶ G) :
    pushR G (resP p v) = spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ v := by sorry
