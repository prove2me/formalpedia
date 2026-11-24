-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FM_cont_inv
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.FM.cont_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:42.353514+00:00
-- url     : https://prove2.me/theorems/0b5c76e3-98c3-4810-b179-1c7ba5d6a05d
-- title:
--   FM: cont inv
-- statement:
--   The FM construction uses the cont inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPfA.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FrameMeasStatementPfA.lean#L13-L19

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.FM.cont_inv {α : Type*} [TopologicalSpace α] {n : ℕ} {f : α → Matrix (Fin n) (Fin n) ℂ}
    (hf : Continuous f) (hd : ∀ a, (f a).det ≠ 0) : Continuous fun a => (f a)⁻¹ := by sorry
