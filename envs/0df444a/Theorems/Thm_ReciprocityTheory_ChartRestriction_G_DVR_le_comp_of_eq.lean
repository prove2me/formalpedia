-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_le_comp_of_eq
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.le_comp_of_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:20.180269+00:00
-- url     : https://prove2.me/theorems/131f74e2-578e-5e7a-b502-0253d100e1fd
-- title:
--   DVR: le comp of eq
-- statement:
--   The DVR construction uses the le comp of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L101-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/MemFinsetInf.lean#L101-L105

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_MemFinsetInf
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

theorem ReciprocityTheory.ChartRestriction.G.DVR.le_comp_of_eq {Z Y Y' X : Scheme.{0}} {f : Z ⟶ Y} {g : Y ⟶ X} {f' : Z ⟶ Y'} {g' : Y' ⟶ X}
    (h : f ≫ g = f' ≫ g') {U : X.Opens} {O : Z.Opens} (hO : O ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U)) :
    O ≤ (f' ≫ g') ⁻¹ᵁ U := by sorry
