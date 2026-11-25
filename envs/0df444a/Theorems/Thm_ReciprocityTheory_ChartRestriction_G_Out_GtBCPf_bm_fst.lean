-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_bm_fst
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.bm_fst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:55:43.519713+00:00
-- url     : https://prove2.me/theorems/2385046b-5dee-4aae-9d63-bb99e35f9e3f
-- title:
--   Gt BCPf: bm fst
-- statement:
--   The Gt BCPf construction uses the bm fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitsEq.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitsEq.lean#L126-L130

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitsEq
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
open Semi Geo.Tor PullGtPf
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X] {G : Over S} [GrpObj G]

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.bm_fst : (fst (splitTorus S' X) ((Over.pullback f).obj G)).left ≫ hT f X =
    bm f X ≫ (fst (splitTorus S X) G).left := by sorry
