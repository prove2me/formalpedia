-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_app_congr_rs
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.app_congr_rs
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:46:37.8448+00:00
-- url     : https://prove2.me/theorems/646e9f1d-8ba2-4134-a182-422c62e2e124
-- title:
--   DVR: app congr rs
-- statement:
--   The DVR construction uses the app congr rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L261-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L261-L264

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.app_congr_rs {Y Z : Scheme.{0}} (φ ψ : Y ⟶ Z) (e : φ = ψ) {U : Z.Opens} {W : Y.Opens} (w : W ≤ φ ⁻¹ᵁ U)
    (w' : W ≤ ψ ⁻¹ᵁ U) (z : Γ(Z, U)) : rs w ((φ.app U).hom z) = rs w' ((ψ.app U).hom z) := by sorry
