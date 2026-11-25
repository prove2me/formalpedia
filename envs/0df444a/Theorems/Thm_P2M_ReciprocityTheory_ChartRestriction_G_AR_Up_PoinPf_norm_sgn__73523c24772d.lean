-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_norm_sgn__73523c24772d
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_norm_sgn__73523c24772d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:55.603417+00:00
-- url     : https://prove2.me/theorems/e1107352-ca14-40c0-869e-b87c18815496
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf norm sgn  73523c24772d: P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf norm sgn  73523c24772d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf norm sgn  73523c24772d construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf norm sgn  73523c24772d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfB.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfB.lean#L101-L103

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_norm_sgn__73523c24772d (p0 a : ℕ) : ‖((sgn p0 a : ℝ) : ℂ)‖ = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«PoinPf».«norm_sgn'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_norm_sgn__73523c24772d
