-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_shape_pull_comp
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.shape_pull_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:19:18.76295+00:00
-- url     : https://prove2.me/theorems/b811bbad-c372-5006-afed-e042daefea89
-- title:
--   DVR: shape pull comp
-- statement:
--   The DVR construction uses the shape pull comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L181-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L181-L188

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' K₂ K₂' : Type} [Fintype K] [Fintype K'] [Fintype K₂] [Fintype K₂']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
  {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₂' : K₂' → (Y ⟶ X)} {ε₂' : K₂' → ℤ}

theorem ReciprocityTheory.ChartRestriction.G.DVR.shape_pull_comp {W : Scheme.{0}} (g : Z ⟶ Y) (g' : W ⟶ Z) {U : Y.Opens} {U₁ : Z.Opens} {V₁ V₂ O : W.Opens}
    (h₁ : U₁ ≤ g ⁻¹ᵁ U) (k₁ : V₁ ≤ g' ⁻¹ᵁ U₁) (k₂ : V₂ ≤ (g' ≫ g) ⁻¹ᵁ U) (o₁ : O ≤ V₁) (o₂ : O ≤ V₂)
    (x : Γ(Y, U)ˣ) :
    res o₁ (res k₁ (pullU g' U₁ (res h₁ (pullU g U x)))) = res o₂ (res k₂ (pullU (g' ≫ g) U x)) := by sorry
