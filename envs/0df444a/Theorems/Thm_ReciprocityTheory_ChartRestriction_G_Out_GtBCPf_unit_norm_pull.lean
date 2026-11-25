-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_unit_norm_pull
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.unit_norm_pull
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:06:40.985742+00:00
-- url     : https://prove2.me/theorems/4e558774-6811-50ed-9f8c-690729d5bdf9
-- title:
--   Gt BCPf: unit norm pull
-- statement:
--   The Gt BCPf construction uses the unit norm pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitNorm.lean#L38-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitNorm.lean#L38-L77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_PreLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_PullbackDegree_EpsPullbackFst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_UnitNorm
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

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.unit_norm_pull {S₁ S₂ Y Z : Scheme.{0}} (e₁ : S₁ ⟶ Y) (e₂ : S₂ ⟶ Z) (a : Z ⟶ Y) (ff : S₂ ⟶ S₁)
    (he : e₂ ≫ a = ff ≫ e₁) {W : Y.Opens} (u : Γ(Y, W)ˣ) {W' : Z.Opens} (hW' : W' ≤ a ⁻¹ᵁ W)
    {V : S₁.Opens} (r : Γ(S₁, V)ˣ) {V' : S₂.Opens} (hV' : V' ≤ ff ⁻¹ᵁ V)
    (h : res (inf_le_left : e₁ ⁻¹ᵁ W ⊓ V ≤ e₁ ⁻¹ᵁ W) (pullU e₁ W u) *
      res (inf_le_right : e₁ ⁻¹ᵁ W ⊓ V ≤ V) r = 1) :
    res (inf_le_left : e₂ ⁻¹ᵁ W' ⊓ V' ≤ e₂ ⁻¹ᵁ W') (pullU e₂ W' (res hW' (pullU a W u))) *
      res (inf_le_right : e₂ ⁻¹ᵁ W' ⊓ V' ≤ V') (res hV' (pullU ff V r)) = 1 := by sorry
