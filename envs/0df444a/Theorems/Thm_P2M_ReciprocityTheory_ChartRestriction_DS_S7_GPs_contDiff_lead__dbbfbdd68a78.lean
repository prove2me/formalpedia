-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiff_lead__dbbfbdd68a78
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiff_lead__dbbfbdd68a78
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:43:19.568134+00:00
-- url     : https://prove2.me/theorems/6dcd86bc-e511-503a-8c8b-914eecd12f91
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS S7 GPs cont Diff lead  dbbfbdd68a78: P2 M Reciprocity Theory Chart Restriction DS S7 GPs cont Diff lead  dbbfbdd68a78
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS S7 GPs cont Diff lead  dbbfbdd68a78 construction uses the P2 M Reciprocity Theory Chart Restriction DS S7 GPs cont Diff lead  dbbfbdd68a78 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/GelfandPsB.lean#L40-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs

theorem P2M_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiff_lead__dbbfbdd68a78 (i : ℕ) : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«S7».«GPs».«contDiff_lead'» := P2M_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiff_lead__dbbfbdd68a78
