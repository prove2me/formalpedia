-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_shape_pull_id
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.shape_pull_id
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:29.177994+00:00
-- url     : https://prove2.me/theorems/90d2453e-ac41-5e84-8c99-a1018297a52a
-- title:
--   DVR: shape pull id
-- statement:
--   The DVR construction uses the shape pull id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L216-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L216-L219

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.shape_pull_id {U : Y.Opens} {V O : Y.Opens} (h : V ≤ (𝟙 Y) ⁻¹ᵁ U) (o : O ≤ V) (o' : O ≤ U) (x : Γ(Y, U)ˣ) :
    res o (res h (pullU (𝟙 Y) U x)) = res o' x := by sorry
