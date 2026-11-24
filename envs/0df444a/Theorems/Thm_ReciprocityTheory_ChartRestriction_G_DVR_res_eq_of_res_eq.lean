-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_res_eq_of_res_eq
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.res_eq_of_res_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:29.266434+00:00
-- url     : https://prove2.me/theorems/a8637a1c-73ab-4f1b-bb62-f21e36d64726
-- title:
--   DVR: res eq of res eq
-- statement:
--   The DVR construction uses the res eq of res eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBCorr.lean#L81-L84

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.res_eq_of_res_eq {U V W : Y.Opens} (a : Γ(Y, U)ˣ) (b : Γ(Y, V)ˣ) (h1 : W ≤ U) (h2 : W ≤ V)
    (h : res (inf_le_left : U ⊓ V ≤ U) a = res (inf_le_right : U ⊓ V ≤ V) b) :
    res h1 a = res h2 b := by sorry
