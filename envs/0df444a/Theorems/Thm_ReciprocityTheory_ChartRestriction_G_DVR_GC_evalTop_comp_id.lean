-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_GC_evalTop_comp_id
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_comp_id
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:10:08.294914+00:00
-- url     : https://prove2.me/theorems/78b65255-99b9-559a-8821-65589d8c499f
-- title:
--   GC: eval Top comp id
-- statement:
--   The GC construction uses the eval Top comp id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L168-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenCalc.lean#L168-L175

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_QuadTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.GC
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.DVR.GC.evalTop_comp_id {A : Type} [CommRing A] {Y : Scheme.{0}} (g₁ : Spec (CommRingCat.of A) ⟶ Y)
    (g₂ : Y ⟶ Spec (CommRingCat.of A)) (h : g₁ ≫ g₂ = 𝟙 _) (hU : g₁ ⁻¹ᵁ (g₂ ⁻¹ᵁ ⊤) = ⊤)
    (y : Γ(Spec (CommRingCat.of A), ⊤)) :
    evalTop _ hU ((g₁.app _).hom ((g₂.app ⊤).hom y)) = evalTop ⊤ rfl y := by sorry
