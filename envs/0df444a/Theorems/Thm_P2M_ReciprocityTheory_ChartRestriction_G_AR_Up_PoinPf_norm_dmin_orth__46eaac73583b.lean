-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_norm_dmin_orth__46eaac73583b
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_norm_dmin_orth__46eaac73583b
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:45:14.40804+00:00
-- url     : https://prove2.me/theorems/90ad444d-0b23-46b0-9ee6-fbe904ccb111
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf norm dmin orth  46eaac73583b: P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf norm dmin orth  46eaac73583b
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf norm dmin orth  46eaac73583b construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf norm dmin orth  46eaac73583b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfB.lean#L105-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfB.lean#L105-L110

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_norm_dmin_orth__46eaac73583b (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ)
    (i : Fin (r + 1)) : ‖dmin X.Gm x τ i‖ = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«PoinPf».«norm_dmin_orth'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_norm_dmin_orth__46eaac73583b
