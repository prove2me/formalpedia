-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_app_rs
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.comp_app_rs
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:50:14.659906+00:00
-- url     : https://prove2.me/theorems/195b115c-144f-4fa0-927b-202b4b57d427
-- title:
--   DVR: comp app rs
-- statement:
--   The DVR construction uses the comp app rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L255-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L255-L259

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RValue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpandsAtScale
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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {G : Over (Spec (CommRingCat.of V))}

theorem ReciprocityTheory.ChartRestriction.G.DVR.comp_app_rs {X Y Z : Scheme.{0}} (φ : Y ⟶ Z) (ψ : Z ⟶ X) {U : X.Opens} {W : Y.Opens}
    (w : W ≤ (φ ≫ ψ) ⁻¹ᵁ U) (w' : W ≤ φ ⁻¹ᵁ (ψ ⁻¹ᵁ U)) (z : Γ(X, U)) :
    rs w (((φ ≫ ψ).app U).hom z) = rs w' ((φ.app (ψ ⁻¹ᵁ U)).hom ((ψ.app U).hom z)) := by sorry
