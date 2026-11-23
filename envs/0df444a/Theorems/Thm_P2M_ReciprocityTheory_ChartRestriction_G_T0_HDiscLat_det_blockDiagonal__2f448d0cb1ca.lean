-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_det_blockDiagonal__2f448d0cb1ca
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_det_blockDiagonal__2f448d0cb1ca
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:19:26.204851+00:00
-- url     : https://prove2.me/theorems/5acacd9e-6610-4441-a3ce-910dee049ded
-- title:
--   P2 M Reciprocity Theory Chart Restriction G T0 HDisc Lat det block Diagonal  2f448d0cb1ca: P2 M Reciprocity Theory Chart Restriction G T0 HDisc Lat det block Diagonal  2f448d0cb1ca
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G T0 HDisc Lat det block Diagonal  2f448d0cb1ca construction uses the P2 M Reciprocity Theory Chart Restriction G T0 HDisc Lat det block Diagonal  2f448d0cb1ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAA.lean#L10-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAA.lean#L10-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
open Module

theorem P2M_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_det_blockDiagonal__2f448d0cb1ca {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    {κ : ι → Type*} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)]
    (M : ∀ c, Matrix (κ c) (κ c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«T0».«HDiscLat».«det_blockDiagonal'» := P2M_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_det_blockDiagonal__2f448d0cb1ca
