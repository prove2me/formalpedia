-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_w_pair
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.w_pair
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:20:54.559344+00:00
-- url     : https://prove2.me/theorems/afa313cb-6fff-535f-86d2-e7a89fc19e9e
-- title:
--   DVR: w pair
-- statement:
--   The DVR construction uses the w pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenAmple.lean#L56-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenAmple.lean#L56-L76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenAmple
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {Y X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
set_option maxHeartbeats 1000000

theorem ReciprocityTheory.ChartRestriction.G.DVR.w_pair (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (hw : w.IsGen) (a a' : L₂.ι) (b b' : L₁.ι) {V : Y.Opens}
    (h : V ≤ ((L₂.pull f₂).U (fun _ => a) ⊓ (L₁.pull f₁).U (fun _ => b)) ⊓
      ((L₂.pull f₂).U (fun _ => a') ⊓ (L₁.pull f₁).U (fun _ => b'))) :
    res (h.trans inf_le_left) (w.s (fun _ => a, fun _ => b)) =
      tr L₂ V f₂ a a' * (tr L₁ V f₁ b b')⁻¹ * res (h.trans inf_le_right) (w.s (fun _ => a', fun _ => b')) := by sorry
