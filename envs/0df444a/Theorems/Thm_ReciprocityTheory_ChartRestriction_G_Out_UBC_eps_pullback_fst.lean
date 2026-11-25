-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_UBC_eps_pullback_fst
-- name    : ReciprocityTheory.ChartRestriction.G.Out.UBC.eps_pullback_fst
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:19:21.600068+00:00
-- url     : https://prove2.me/theorems/2ff02515-470c-4a14-847f-5f379797e1bc
-- title:
--   UBC: eps pullback fst
-- statement:
--   The UBC construction uses the eps pullback fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullbackDegree/EpsPullbackFst.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullbackDegree/EpsPullbackFst.lean#L37-L45

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

theorem ReciprocityTheory.ChartRestriction.G.Out.UBC.eps_pullback_fst {S S' : Scheme.{0}} (f : S' ⟶ S) :
    (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫ pullback.fst (𝟙_ (Over S)).hom f = f := by sorry
