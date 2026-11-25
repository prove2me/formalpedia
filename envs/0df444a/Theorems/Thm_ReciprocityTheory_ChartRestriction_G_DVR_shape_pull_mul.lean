-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_shape_pull_mul
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.shape_pull_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:26.800665+00:00
-- url     : https://prove2.me/theorems/84e76b60-b97c-5541-ade2-7e64bf9a91c5
-- title:
--   DVR: shape pull mul
-- statement:
--   The DVR construction uses the shape pull mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L166-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L166-L172

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.shape_pull_mul (g : Z ⟶ Y) {U₁ U₂ W : Y.Opens} {Wz W₁ W₂ O Ow : Z.Opens}
    (h₁ : W ≤ U₁) (h₂ : W ≤ U₂) (hz : Wz ≤ g ⁻¹ᵁ W) (hO : O ≤ Wz) (k₁ : W₁ ≤ g ⁻¹ᵁ U₁) (k₂ : W₂ ≤ g ⁻¹ᵁ U₂)
    (m₁ : Ow ≤ W₁) (m₂ : Ow ≤ W₂) (o : O ≤ Ow) (a : Γ(Y, U₁)ˣ) (b : Γ(Y, U₂)ˣ) :
    res hO (res hz (pullU g W (res h₁ a * res h₂ b))) =
      res o (res m₁ (res k₁ (pullU g U₁ a)) * res m₂ (res k₂ (pullU g U₂ b))) := by sorry
