-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tr_pull
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.tr_pull
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:12:35.449639+00:00
-- url     : https://prove2.me/theorems/0095d492-579e-5ccc-95cf-aa8821c1c829
-- title:
--   DVR: tr pull
-- statement:
--   The DVR construction uses the tr pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L71-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L71-L75

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
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
variable {X Y Z : Scheme.{0}} (L : LB X)

theorem ReciprocityTheory.ChartRestriction.G.DVR.tr_pull (h : Z ⟶ Y) {W : Y.Opens} {V : Z.Opens} (hV : V ≤ h ⁻¹ᵁ W) {ψ : Y ⟶ X} {a b : L.ι}
    (hW : W ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b)) :
    res hV (pullU h W (tr L W ψ a b)) = tr L V (h ≫ ψ) a b := by sorry
