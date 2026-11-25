-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_scal_pull
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.scal_pull
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:57:52.891814+00:00
-- url     : https://prove2.me/theorems/5a704122-97a6-50c2-b35d-bbe98730dc19
-- title:
--   DVR: scal pull
-- statement:
--   The DVR construction uses the scal pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L180-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExpandsAtScale.lean#L180-L183

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.scal_pull {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (pY : Y ⟶ Spec (CommRingCat.of V)) (pZ : Z ⟶ Spec (CommRingCat.of V))
    (hφ : φ ≫ pZ = pY) (r : V) : φ.appTop.hom (scal pZ r) = scal pY r := by sorry
