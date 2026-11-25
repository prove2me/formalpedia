-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_toBlocks___mul_2640c3b66a1c
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_toBlocks___mul_2640c3b66a1c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:12.082252+00:00
-- url     : https://prove2.me/theorems/26e422f0-909c-57b0-a10e-18be0f9abeb9
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up KU to Blocks   mul 2640c3b66a1c: P2 M Reciprocity Theory Chart Restriction G AR Up KU to Blocks   mul 2640c3b66a1c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up KU to Blocks   mul 2640c3b66a1c construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up KU to Blocks   mul 2640c3b66a1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfA.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfA.lean#L21-L23

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_toBlocks___mul_2640c3b66a1c {p q : ℕ} (g M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    (g * M).toBlocks₂₂ = g.toBlocks₂₁ * M.toBlocks₁₂ + g.toBlocks₂₂ * M.toBlocks₂₂ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«KU».«toBlocks₂₂_mul» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_toBlocks___mul_2640c3b66a1c
