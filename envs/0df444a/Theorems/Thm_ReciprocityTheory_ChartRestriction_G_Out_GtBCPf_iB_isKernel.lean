-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_iB_isKernel
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.iB_isKernel
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:35:46.254808+00:00
-- url     : https://prove2.me/theorems/34cf9d73-8c53-4e90-afe1-0ed6cc2ef58f
-- title:
--   Gt BCPf: i B is Kernel
-- statement:
--   The Gt BCPf construction uses the i B is Kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/IBIsKernel.lean#L194-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/IBIsKernel.lean#L194-L242

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PullbackSquarePartialSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_IBIsKernel
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
variable {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X]
variable {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B)
variable (i : splitTorus S X ⟶ G)

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.iB_isKernel (hk : IsPullback i (toUnit _) q η[B]) :
    IsPullback (iB f X i) (toUnit _) (qB f q) η[(Over.pullback f).obj B] := by sorry
