-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_UBC_toBase_eq_symm
-- name    : ReciprocityTheory.ChartRestriction.G.Out.UBC.toBase_eq_symm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:30:23.561804+00:00
-- url     : https://prove2.me/theorems/b84c8279-e93a-5999-8966-9bdb4528ef3d
-- title:
--   UBC: to Base eq symm
-- statement:
--   The UBC construction uses the to Base eq symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullbackDegree/EpsPullbackFst.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullbackDegree/EpsPullbackFst.lean#L31-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_UnifBaseChangeInjOfSeamsCS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullbackDegree_EpsPullbackFst
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.UBC
open Semi

theorem ReciprocityTheory.ChartRestriction.G.Out.UBC.toBase_eq_symm {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) (T : Over S')
    (x : T ⟶ (Over.pullback f).obj A) :
    toBase (pullback.condition : pullback.fst A.hom f ≫ A.hom = pullback.snd A.hom f ≫ f) x =
      ((Over.mapPullbackAdj f).homEquiv T A).symm x := by sorry
