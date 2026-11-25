-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_comp
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.corr_pullGen_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:21.675175+00:00
-- url     : https://prove2.me/theorems/0dc8f39c-e485-471f-9c8a-b84026c356f0
-- title:
--   DVR: corr pull Gen comp
-- statement:
--   The DVR construction uses the corr pull Gen comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L190-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L190-L194

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.corr_pullGen_comp {W : Scheme.{0}} (t : LB.Gen (LB.LinComb L φ ε)) (g : Z ⟶ Y) (g' : W ⟶ Z) :
    LB.Gen.Corr L _ ε _ ε (LB.pullGen L _ ε (LB.pullGen L φ ε t g) g') (LB.pullGen L φ ε t (g' ≫ g)) := by sorry
