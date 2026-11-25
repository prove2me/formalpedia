-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__contDiff_6418abd5f35f
-- name    : P2M_ReciprocityTheory_AnForm_A_k__contDiff_6418abd5f35f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:23.321589+00:00
-- url     : https://prove2.me/theorems/0477e74d-2fca-56c2-95a6-8e8264671163
-- title:
--   P2 M Reciprocity Theory An Form A k  cont Diff 6418abd5f35f: P2 M Reciprocity Theory An Form A k  cont Diff 6418abd5f35f
-- statement:
--   The P2 M Reciprocity Theory An Form A k  cont Diff 6418abd5f35f construction uses the P2 M Reciprocity Theory An Form A k  cont Diff 6418abd5f35f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L97-L99

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

theorem P2M_ReciprocityTheory_AnForm_A_k__contDiff_6418abd5f35f : ContDiff ℝ ∞ kθ := by sorry

alias «ReciprocityTheory».«AnForm».«A».«kθ_contDiff» := P2M_ReciprocityTheory_AnForm_A_k__contDiff_6418abd5f35f
