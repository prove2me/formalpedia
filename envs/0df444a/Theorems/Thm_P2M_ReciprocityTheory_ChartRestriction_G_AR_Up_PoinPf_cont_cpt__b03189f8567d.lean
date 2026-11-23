-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_cont_cpt__b03189f8567d
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_cont_cpt__b03189f8567d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:22.064245+00:00
-- url     : https://prove2.me/theorems/7f3aebb1-6f88-42ce-96c4-b841f023fbfb
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf cont cpt  b03189f8567d: P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf cont cpt  b03189f8567d
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf cont cpt  b03189f8567d construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf cont cpt  b03189f8567d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfC.lean#L34-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfC.lean#L34-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfC
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

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_cont_cpt__b03189f8567d (X : Data E r) (x0 : Frame X.Ψ r) : Continuous (cpt X x0) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«PoinPf».«cont_cpt'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_cont_cpt__b03189f8567d
