-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_zpow_sum__eeea0ab3dee3
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_zpow_sum__eeea0ab3dee3
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:58:21.088901+00:00
-- url     : https://prove2.me/theorems/d95d049d-216e-41e8-9a50-0ed97fb82035
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Out Cube Pf zpow sum  eeea0ab3dee3: P2 M Reciprocity Theory Chart Restriction G Out Cube Pf zpow sum  eeea0ab3dee3
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Out Cube Pf zpow sum  eeea0ab3dee3 construction uses the P2 M Reciprocity Theory Chart Restriction G Out Cube Pf zpow sum  eeea0ab3dee3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/Transfer.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/CubePullbacks/Transfer.lean#L21-L25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_CubePullbacks_Transfer
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.CubePf
open Semi

theorem P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_zpow_sum__eeea0ab3dee3 {M : Type} [CommGroup M] {K : Type} (a : M) (s : Finset K) (f : K → ℤ) :
    a ^ (∑ k ∈ s, f k) = ∏ k ∈ s, a ^ f k := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Out».«CubePf».«zpow_sum'» := P2M_ReciprocityTheory_ChartRestriction_G_Out_CubePf_zpow_sum__eeea0ab3dee3
