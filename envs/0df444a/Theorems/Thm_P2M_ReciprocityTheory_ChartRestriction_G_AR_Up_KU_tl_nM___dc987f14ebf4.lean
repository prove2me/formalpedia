-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_nM___dc987f14ebf4
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_nM___dc987f14ebf4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:18:10.88842+00:00
-- url     : https://prove2.me/theorems/7e319923-7512-4653-9c9c-275e39f10c9a
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up KU tl n M   dc987f14ebf4: P2 M Reciprocity Theory Chart Restriction G AR Up KU tl n M   dc987f14ebf4
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up KU tl n M   dc987f14ebf4 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up KU tl n M   dc987f14ebf4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfA.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfA.lean#L86-L87

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_nM___dc987f14ebf4 (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : (tl X (ExF.nM X z τ)).toBlocks₂₂ = ExF.n1 X z τ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«KU».«tl_nM₂₂» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_nM___dc987f14ebf4
