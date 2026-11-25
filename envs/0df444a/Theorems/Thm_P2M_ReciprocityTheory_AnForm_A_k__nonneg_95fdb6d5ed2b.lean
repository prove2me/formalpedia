-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__nonneg_95fdb6d5ed2b
-- name    : P2M_ReciprocityTheory_AnForm_A_k__nonneg_95fdb6d5ed2b
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:29.804568+00:00
-- url     : https://prove2.me/theorems/dd6ea2fc-832f-5f52-b929-b6f0b3a2a000
-- title:
--   P2 M Reciprocity Theory An Form A k  nonneg 95fdb6d5ed2b: P2 M Reciprocity Theory An Form A k  nonneg 95fdb6d5ed2b
-- statement:
--   The P2 M Reciprocity Theory An Form A k  nonneg 95fdb6d5ed2b construction uses the P2 M Reciprocity Theory An Form A k  nonneg 95fdb6d5ed2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L91-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L91-L93

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem P2M_ReciprocityTheory_AnForm_A_k__nonneg_95fdb6d5ed2b (x : ℝ) : 0 ≤ kθ x := by sorry

alias «ReciprocityTheory».«AnForm».«A».«kθ_nonneg» := P2M_ReciprocityTheory_AnForm_A_k__nonneg_95fdb6d5ed2b
