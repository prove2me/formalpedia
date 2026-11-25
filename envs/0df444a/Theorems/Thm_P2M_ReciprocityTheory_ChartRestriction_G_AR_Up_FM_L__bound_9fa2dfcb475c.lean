-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_L__bound_9fa2dfcb475c
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_L__bound_9fa2dfcb475c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:16:20.594164+00:00
-- url     : https://prove2.me/theorems/013c0b1a-8edb-4702-b7bb-935f5b076fda
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up FM L  bound 9fa2dfcb475c: P2 M Reciprocity Theory Chart Restriction G AR Up FM L  bound 9fa2dfcb475c
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up FM L  bound 9fa2dfcb475c construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up FM L  bound 9fa2dfcb475c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPfB.lean#L20-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPfB.lean#L20-L47

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FrameMeasStatementPfB
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
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_L__bound_9fa2dfcb475c {C : Set (Frame X.Ψ r)} (hCd : C ⊆ X.dom) {R0 : ℝ}
    (hR0 : ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0) {p : Frame X.Ψ r} (hp : p ∈ X.dom)
    {y : UpI X.Ψ r → ℂ} (hy : ∀ τ b, y (dI τ b) ≠ 0) (hx : rmul p (UF X y) ∈ C) (i : UpI X.Ψ r) :
    ‖Lβ (β0 X p) y i‖ ≤ R0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«FM».«Lβ_bound» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_L__bound_9fa2dfcb475c
