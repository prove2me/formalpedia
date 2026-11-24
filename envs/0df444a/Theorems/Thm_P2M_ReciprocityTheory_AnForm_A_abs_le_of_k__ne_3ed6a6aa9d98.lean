-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_abs_le_of_k__ne_3ed6a6aa9d98
-- name    : P2M_ReciprocityTheory_AnForm_A_abs_le_of_k__ne_3ed6a6aa9d98
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:17.3548+00:00
-- url     : https://prove2.me/theorems/90e11574-4acf-44d0-a589-8ca0f0c3a3fe
-- title:
--   P2 M Reciprocity Theory An Form A abs le of k  ne 3ed6a6aa9d98: P2 M Reciprocity Theory An Form A abs le of k  ne 3ed6a6aa9d98
-- statement:
--   The P2 M Reciprocity Theory An Form A abs le of k  ne 3ed6a6aa9d98 construction uses the P2 M Reciprocity Theory An Form A abs le of k  ne 3ed6a6aa9d98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/ContinuousTmaxShift.lean#L103-L107

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

theorem P2M_ReciprocityTheory_AnForm_A_abs_le_of_k__ne_3ed6a6aa9d98 {x : ℝ} (h : kθ x ≠ 0) : |x| ≤ 1 / 2 := by sorry

alias «ReciprocityTheory».«AnForm».«A».«abs_le_of_kθ_ne» := P2M_ReciprocityTheory_AnForm_A_abs_le_of_k__ne_3ed6a6aa9d98
