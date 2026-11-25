-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_rs_app_pullGen
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.rs_app_pullGen
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:32:23.874976+00:00
-- url     : https://prove2.me/theorems/73c60f55-9465-4ed8-ad57-b8bfce243582
-- title:
--   DVR: rs app pull Gen
-- statement:
--   The DVR construction uses the rs app pull Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RsAppPullGen.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RsAppPullGen.lean#L88-L92

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExpIdentRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_RsAppPullGen
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
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {X Y Y' Z : Scheme.{0}} (L : LB X) {K₁ K₂ K₃ K K' : Type} [Fintype K₁] [Fintype K₂] [Fintype K₃]
  [Fintype K] [Fintype K']

theorem ReciprocityTheory.ChartRestriction.G.DVR.rs_app_pullGen {W : Scheme.{0}} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε))
    (g : W ⟶ Y) (j : K → L.ι) (q : Z ⟶ W) {O : Z.Opens}
    (h : O ≤ q ⁻¹ᵁ LB.wchart L (fun k => g ≫ φ k) j) (h' : O ≤ (q ≫ g) ⁻¹ᵁ LB.wchart L φ j) :
    rs h ((q.app _).hom ((LB.pullGen L φ ε c g).s j).val) = rs h' (((q ≫ g).app _).hom (c.s j).val) := by sorry
