-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TG_appLE_res
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.TG.appLE_res
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:46.690062+00:00
-- url     : https://prove2.me/theorems/ec395a95-6c7f-5236-99b6-85a76741e336
-- title:
--   TG: app LE res
-- statement:
--   The TG construction uses the app LE res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenDiv.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ThetaGenDiv.lean#L17-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenLevel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGenDiv
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
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TG
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem ReciprocityTheory.ChartRestriction.G.DVR.TG.appLE_res {X Y : Scheme.{0}} (i0 : X ⟶ Y) {V1 W : Y.Opens} {V0 : X.Opens} (hV : V0 ≤ i0 ⁻¹ᵁ V1)
    (h1 : V1 ≤ W) (h0 : V0 ≤ i0 ⁻¹ᵁ W) (y : Γ(Y, W)) :
    (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom y) =
      (X.presheaf.map (homOfLE h0).op).hom ((i0.app W).hom y) := by sorry
