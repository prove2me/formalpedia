-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_bor___36e688b9c17f
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_bor___36e688b9c17f
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:41.012808+00:00
-- url     : https://prove2.me/theorems/9cf9498d-11d1-4573-a817-d71480ecfb55
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up KU tl bor   36e688b9c17f: P2 M Reciprocity Theory Chart Restriction G AR Up KU tl bor   36e688b9c17f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up KU tl bor   36e688b9c17f construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up KU tl bor   36e688b9c17f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfA.lean#L95-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfA.lean#L95-L101

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_bor___36e688b9c17f (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) :
    (tl X (mat b τ)).toBlocks₁₂ = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«KU».«tl_bor₁₂» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_tl_bor___36e688b9c17f
