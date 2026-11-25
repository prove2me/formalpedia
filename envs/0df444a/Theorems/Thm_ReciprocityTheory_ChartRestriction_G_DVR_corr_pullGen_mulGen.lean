-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_mulGen
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.corr_pullGen_mulGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:37.847666+00:00
-- url     : https://prove2.me/theorems/cf655dcc-01b7-404a-9b8d-3bffef9a4120
-- title:
--   DVR: corr pull Gen mul Gen
-- statement:
--   The DVR construction uses the corr pull Gen mul Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L174-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L174-L179

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.corr_pullGen_mulGen (t : LB.Gen (LB.LinComb L φ ε)) (t₂ : LB.Gen (LB.LinComb L φ₂ ε₂)) (g : Z ⟶ Y) :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (LB.mulGen L _ _ _ _ t t₂) g)
      (LB.mulGen L _ _ _ _ (LB.pullGen L φ ε t g) (LB.pullGen L φ₂ ε₂ t₂ g)) := by sorry
