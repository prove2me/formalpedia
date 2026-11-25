-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_pnorm_orth__e2bbf64ac7ff
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_pnorm_orth__e2bbf64ac7ff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:14:38.120741+00:00
-- url     : https://prove2.me/theorems/e74b120c-e446-4975-bd2c-d1564dc230f2
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf pnorm orth  e2bbf64ac7ff: P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf pnorm orth  e2bbf64ac7ff
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf pnorm orth  e2bbf64ac7ff construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf pnorm orth  e2bbf64ac7ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfB.lean#L112-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfB.lean#L112-L115

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_pnorm_orth__e2bbf64ac7ff (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r}
    (hx : IsOrth X x) : X.pnorm la P x = ‖P x‖ := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«PoinPf».«pnorm_orth'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_pnorm_orth__e2bbf64ac7ff
