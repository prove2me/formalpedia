-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_UBC_eSec_pullback
-- name    : ReciprocityTheory.ChartRestriction.G.Out.UBC.eSec_pullback
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:25:32.475257+00:00
-- url     : https://prove2.me/theorems/4e0e23c7-1486-421b-a1fc-9ad16d141223
-- title:
--   UBC: e Sec pullback
-- statement:
--   The UBC construction uses the e Sec pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullbackDegree/EpsPullbackFst.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullbackDegree/EpsPullbackFst.lean#L47-L51

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

theorem ReciprocityTheory.ChartRestriction.G.Out.UBC.eSec_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (A : Over S) [GrpObj A] :
    eSec ((Over.pullback f).obj A) ≫ pullback.fst A.hom f = f ≫ eSec A := by sorry
