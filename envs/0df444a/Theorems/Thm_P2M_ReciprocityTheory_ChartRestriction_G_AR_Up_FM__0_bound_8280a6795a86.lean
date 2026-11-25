-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM__0_bound_8280a6795a86
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM__0_bound_8280a6795a86
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:14:30.285202+00:00
-- url     : https://prove2.me/theorems/479c60d5-71c3-4529-a9d7-22f157e11602
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up FM  0 bound 8280a6795a86: P2 M Reciprocity Theory Chart Restriction G AR Up FM  0 bound 8280a6795a86
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up FM  0 bound 8280a6795a86 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up FM  0 bound 8280a6795a86 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPfA.lean#L77-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPfA.lean#L77-L100

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FM
open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM__0_bound_8280a6795a86 {C : Set (Frame X.Ψ r)} (hC : IsCompact C) (hCd : C ⊆ X.dom) :
    ∃ R0 : ℝ, ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«FM».«β0_bound» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM__0_bound_8280a6795a86
