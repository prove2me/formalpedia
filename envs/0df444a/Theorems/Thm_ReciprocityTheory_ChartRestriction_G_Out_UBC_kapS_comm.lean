-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_UBC_kapS_comm
-- name    : ReciprocityTheory.ChartRestriction.G.Out.UBC.kapS_comm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:25:09.451352+00:00
-- url     : https://prove2.me/theorems/a4330ce3-835e-4bc9-8099-0f5257a86148
-- title:
--   UBC: kap S comm
-- statement:
--   The UBC construction uses the kap S comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullbackDegree/EpsPullbackFst.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/PullbackDegree/EpsPullbackFst.lean#L135-L139

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
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
variable (φ : R →+* R') (hφ : Function.Injective φ)

theorem ReciprocityTheory.ChartRestriction.G.Out.UBC.kapS_comm : kapS φ hφ ≫ jK R = jK R' ≫ specOf φ := by sorry
