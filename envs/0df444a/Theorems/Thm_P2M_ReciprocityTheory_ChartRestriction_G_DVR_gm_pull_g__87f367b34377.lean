-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_gm_pull_g__87f367b34377
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_gm_pull_g__87f367b34377
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:15:00.896304+00:00
-- url     : https://prove2.me/theorems/bd539bc0-3807-449e-9146-6eb26ac48fb1
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR gm pull g  87f367b34377: P2 M Reciprocity Theory Chart Restriction G DVR gm pull g  87f367b34377
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR gm pull g  87f367b34377 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR gm pull g  87f367b34377 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenAmple.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/GenAmple.lean#L83-L88

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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_gm_pull_g__87f367b34377 {Z : Scheme.{0}} {X : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (r : Z ⟶ Y) (z : Z) (a b : L.ι)
    (ha : f (r z) ∈ L.U a) (hb : f (r z) ∈ L.U b) :
    gm r z ((L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b)) ((L.pull f).g (fun _ => a) (fun _ => b)) =
      gm (r ≫ f) z (L.U a ⊓ L.U b) (L.g a b) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«gm_pull_g'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_gm_pull_g__87f367b34377
