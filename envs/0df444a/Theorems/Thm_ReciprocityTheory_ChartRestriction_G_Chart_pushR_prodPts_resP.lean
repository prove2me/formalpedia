-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pushR_prodPts_resP
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.pushR_prodPts_resP
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:36:21.654585+00:00
-- url     : https://prove2.me/theorems/67e522b0-7ecd-49a9-b47e-2277186b4071
-- title:
--   Chart: push R prod Pts res P
-- statement:
--   The Chart construction uses the push R prod Pts res P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PushRProdPtsResP.lean#L40-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PushRProdPtsResP.lean#L40-L53

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

theorem ReciprocityTheory.ChartRestriction.G.Chart.pushR_prodPts_resP {d : ℕ} (c : Fin d → S) (u : Fin d → (sp (R₀ := S) (DualNumber S) ⟶ G)) :
    pushR G (prodPts (fun i => algebraMap S (Localization.AtPrime p) (c i)) (fun i => resP p (u i))) =
      spMap (dualMapS (Algebra.ofId S (Localization.AtPrime p))) ≫ prodPts c u := by sorry
