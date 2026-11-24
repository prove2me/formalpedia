-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_hasFDerivAt_comp_smul__eb59e24e54e1
-- name    : P2M_ReciprocityTheory_AnForm_A_hasFDerivAt_comp_smul__eb59e24e54e1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:31.408627+00:00
-- url     : https://prove2.me/theorems/4de2d211-167f-4086-adbc-28942afe9ea2
-- title:
--   P2 M Reciprocity Theory An Form A has FDeriv At comp smul  eb59e24e54e1: P2 M Reciprocity Theory An Form A has FDeriv At comp smul  eb59e24e54e1
-- statement:
--   The P2 M Reciprocity Theory An Form A has FDeriv At comp smul  eb59e24e54e1 construction uses the P2 M Reciprocity Theory An Form A has FDeriv At comp smul  eb59e24e54e1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L100-L104

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
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
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem P2M_ReciprocityTheory_AnForm_A_hasFDerivAt_comp_smul__eb59e24e54e1 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : (ι → ℝ) → F} (c : ℝ) (t : ι → ℝ) (hg : DifferentiableAt ℝ g (c • t)) :
    HasFDerivAt (fun t => g (c • t)) (c • fderiv ℝ g (c • t)) t := by sorry

alias «ReciprocityTheory».«AnForm».«A».«hasFDerivAt_comp_smul'» := P2M_ReciprocityTheory_AnForm_A_hasFDerivAt_comp_smul__eb59e24e54e1
