-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_refl__cb32e03a41c1
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_refl__cb32e03a41c1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:05.126027+00:00
-- url     : https://prove2.me/theorems/13eb54b7-f6fc-479f-9889-cf5df6dbd36d
-- title:
--   P2 M Reciprocity Theory Chart Restriction G DVR res refl  cb32e03a41c1: P2 M Reciprocity Theory Chart Restriction G DVR res refl  cb32e03a41c1
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G DVR res refl  cb32e03a41c1 construction uses the P2 M Reciprocity Theory Chart Restriction G DVR res refl  cb32e03a41c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L87-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBTransport.lean#L87-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBTransport
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
open scoped Classical
variable {X Y : Scheme.{0}} (L : LB X)

theorem P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_refl__cb32e03a41c1 {Z : Scheme.{0}} {U : Z.Opens} (x : Γ(Z, U)ˣ) : res (le_refl U) x = x := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«DVR».«res_refl'» := P2M_ReciprocityTheory_ChartRestriction_G_DVR_res_refl__cb32e03a41c1
