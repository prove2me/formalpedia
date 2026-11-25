-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_iB_hom
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.iB_hom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:35:17.434002+00:00
-- url     : https://prove2.me/theorems/590f8ce7-6111-4057-92aa-d3b5ce0e212e
-- title:
--   Gt BCPf: i B hom
-- statement:
--   The Gt BCPf construction uses the i B hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/IBIsKernel.lean#L118-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/IBIsKernel.lean#L118-L166

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

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.iB_hom [IsMonHom i] : IsMonHom (iB f X i) := by sorry
