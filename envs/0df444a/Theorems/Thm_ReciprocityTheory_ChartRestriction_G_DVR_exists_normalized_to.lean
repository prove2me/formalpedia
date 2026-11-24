-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_normalized_to
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.exists_normalized_to
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:30.559094+00:00
-- url     : https://prove2.me/theorems/46f2e617-d3e7-4446-af0b-182331c11c10
-- title:
--   DVR: exists normalized to
-- statement:
--   The DVR construction uses the exists normalized to property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L277-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L277-L308

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.exists_normalized_to {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K Kr : Type} [Fintype K] [Fintype Kr]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (p : Y ⟶ Z) (z : Z ⟶ Y) (hzp : z ≫ p = 𝟙 Z)
    (φr : Kr → (Z ⟶ X)) (εr : Kr → ℤ) (r : LB.Gen (LB.LinComb L φr εr)) (hr : r.IsGen)
    (h0 : fsum (fun k => z ≫ φ k) ε = fsum φr εr) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' z) r := by sorry
