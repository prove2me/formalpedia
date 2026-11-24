-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_lact_rmul__da3d10a12e1f
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_lact_rmul__da3d10a12e1f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:52.984989+00:00
-- url     : https://prove2.me/theorems/09103f66-bc87-4a67-843c-a7637d361f63
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up KU lact rmul  da3d10a12e1f: P2 M Reciprocity Theory Chart Restriction G AR Up KU lact rmul  da3d10a12e1f
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up KU lact rmul  da3d10a12e1f construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up KU lact rmul  da3d10a12e1f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfC.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfC.lean#L152-L156

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfC
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
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instMSMat
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instBorelMat
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instSCMat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
attribute [local instance] ReciprocityTheory.ChartRestriction.G.AR.Up.KU.instPolishFrame

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_lact_rmul__da3d10a12e1f (X : Data E r) (γ : GL (Fin r) E) (x b : Frame X.Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«KU».«lact_rmul'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_lact_rmul__da3d10a12e1f
