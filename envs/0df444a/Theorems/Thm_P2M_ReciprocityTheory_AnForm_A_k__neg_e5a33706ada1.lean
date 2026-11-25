-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_k__neg_e5a33706ada1
-- name    : P2M_ReciprocityTheory_AnForm_A_k__neg_e5a33706ada1
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:38.554886+00:00
-- url     : https://prove2.me/theorems/10add467-f644-4e5a-bcd4-636d31e1d783
-- title:
--   P2 M Reciprocity Theory An Form A k  neg e5a33706ada1: P2 M Reciprocity Theory An Form A k  neg e5a33706ada1
-- statement:
--   The P2 M Reciprocity Theory An Form A k  neg e5a33706ada1 construction uses the P2 M Reciprocity Theory An Form A k  neg e5a33706ada1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L94-L96

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

theorem P2M_ReciprocityTheory_AnForm_A_k__neg_e5a33706ada1 (x : ℝ) : kθ (-x) = kθ x := by sorry

alias «ReciprocityTheory».«AnForm».«A».«kθ_neg» := P2M_ReciprocityTheory_AnForm_A_k__neg_e5a33706ada1
