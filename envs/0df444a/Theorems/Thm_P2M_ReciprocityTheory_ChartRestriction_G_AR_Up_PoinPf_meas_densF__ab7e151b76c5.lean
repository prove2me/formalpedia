-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_meas_densF__ab7e151b76c5
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_meas_densF__ab7e151b76c5
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:15:12.033853+00:00
-- url     : https://prove2.me/theorems/f832773f-e7ac-49ba-a6eb-ee3a134a7737
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf meas dens F  ab7e151b76c5: P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf meas dens F  ab7e151b76c5
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf meas dens F  ab7e151b76c5 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf meas dens F  ab7e151b76c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfI.lean#L64-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfI.lean#L64-L74

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_meas_densF__ab7e151b76c5 (X : Data E r) (x' : Frame X.Ψ r) :
    Measurable fun w => ENNReal.ofReal (densF X x' w) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«PoinPf».«meas_densF'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_meas_densF__ab7e151b76c5
