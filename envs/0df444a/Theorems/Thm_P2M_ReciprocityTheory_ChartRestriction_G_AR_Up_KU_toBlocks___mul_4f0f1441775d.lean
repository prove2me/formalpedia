-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_toBlocks___mul_4f0f1441775d
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_toBlocks___mul_4f0f1441775d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:25.859338+00:00
-- url     : https://prove2.me/theorems/f9c67613-165c-5b6f-a268-3ab0b95fe5c9
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up KU to Blocks   mul 4f0f1441775d: P2 M Reciprocity Theory Chart Restriction G AR Up KU to Blocks   mul 4f0f1441775d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up KU to Blocks   mul 4f0f1441775d construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up KU to Blocks   mul 4f0f1441775d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfA.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfA.lean#L17-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_toBlocks___mul_4f0f1441775d {p q : ℕ} (g M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    (g * M).toBlocks₁₂ = g.toBlocks₁₁ * M.toBlocks₁₂ + g.toBlocks₁₂ * M.toBlocks₂₂ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«KU».«toBlocks₁₂_mul» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_toBlocks___mul_4f0f1441775d
