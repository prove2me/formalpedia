-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_gU_rp_rp
-- name    : ReciprocityTheory.ChartRestriction.G.Out.LBxP.gU_rp_rp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:31:38.0499+00:00
-- url     : https://prove2.me/theorems/d0362d93-ef1d-5e25-8fe6-5a749523416e
-- title:
--   LBx P: g U rp rp
-- statement:
--   The LBx P construction uses the g U rp rp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/GeneratorPullback/PullAlong.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/GeneratorPullback/PullAlong.lean#L36-L41

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_pullU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.LBxP
open Semi
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res gU_pullU gU_pullU_congr gU_pullU_res pullU_res')
variable {X X' Y Y' Z Z' : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Out.LBxP.gU_rp_rp (a : Z ⟶ Y) (h : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (hV : V ≤ h ⁻¹ᵁ U)
    {W : Z.Opens} (hW : W ≤ a ⁻¹ᵁ V) (u : Γ(X, U)ˣ) (z : Z) (hz : z ∈ W) :
    gU z hz (res hW (pullU a V (res hV (pullU h U u)))) =
      gU z (show z ∈ (a ≫ h) ⁻¹ᵁ U from hV (hW hz)) (pullU (a ≫ h) U u) := by sorry
