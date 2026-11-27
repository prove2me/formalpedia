-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_equivPullL
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.equivPullL
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T18:01:25.684894+00:00
-- url     : https://prove2.me/theorems/1e9744ef-331e-4c32-a1a5-3162f7f04e17
-- title:
--   Gt BCPf: equiv Pull L
-- statement:
--   The Gt BCPf construction uses the equiv Pull L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitsEq.lean#L38-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/UnitsEq.lean#L38-L72

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

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.equivPullL {T₁ T₂ Y Z P₁ P₂ : Scheme.{0}} (act₁ s₁ : P₁ ⟶ Y) (f₁ : P₁ ⟶ T₁)
    (act₂ s₂ : P₂ ⟶ Z) (f₂ : P₂ ⟶ T₂) (b : P₂ ⟶ P₁) (a : Z ⟶ Y) (h : T₂ ⟶ T₁)
    (W : Y.Opens) (u : Γ(Y, W)ˣ) (W' : Z.Opens) (hW' : W' ≤ a ⁻¹ᵁ W)
    (c : Γ(T₁, ⊤)ˣ) (c' : Γ(T₂, ⊤)ˣ)
    (hc : res (fun _ _ => trivial : (⊤ : T₂.Opens) ≤ h ⁻¹ᵁ ⊤) (pullU h ⊤ c) = c')
    (le₁ : s₁ ⁻¹ᵁ W ≤ act₁ ⁻¹ᵁ W) (t₁ : s₁ ⁻¹ᵁ W ≤ f₁ ⁻¹ᵁ ⊤)
    (H : res le₁ (pullU act₁ W u) = res t₁ (pullU f₁ ⊤ c) * pullU s₁ W u)
    (ha : act₂ ≫ a = b ≫ act₁) (hs : s₂ ≫ a = b ≫ s₁) (hf : f₂ ≫ h = b ≫ f₁)
    (le₂ : s₂ ⁻¹ᵁ W' ≤ act₂ ⁻¹ᵁ W') (t₂ : s₂ ⁻¹ᵁ W' ≤ f₂ ⁻¹ᵁ ⊤) :
    res le₂ (pullU act₂ W' (res hW' (pullU a W u))) =
      res t₂ (pullU f₂ ⊤ c') * pullU s₂ W' (res hW' (pullU a W u)) := by sorry
