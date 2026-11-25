-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_app_comp__dd8acccb3343
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_app_comp__dd8acccb3343
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:36:58.853076+00:00
-- url     : https://prove2.me/theorems/8ae17f62-968a-4572-8866-c886a7757a78
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR rs app comp  dd8acccb3343: P2 M Reciprocity Theory Chart Restriction G DVR rs app comp  dd8acccb3343
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR rs app comp  dd8acccb3343 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR rs app comp  dd8acccb3343 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RsAppPullGen.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/RsAppPullGen.lean#L71-L75

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_app_comp__dd8acccb3343 {Z Y X : Scheme.{0}} (h : Z ⟶ Y) (ψ : Y ⟶ X) {U : X.Opens} {W : Y.Opens}
    {V : Z.Opens} (hW : W ≤ ψ ⁻¹ᵁ U) (hV : V ≤ h ⁻¹ᵁ W) (hV' : V ≤ (h ≫ ψ) ⁻¹ᵁ U) (x : Γ(X, U)) :
    rs hV ((h.app W).hom (rs hW ((ψ.app U).hom x))) = rs hV' (((h ≫ ψ).app U).hom x) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«rs_app_comp'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_rs_app_comp__dd8acccb3343
