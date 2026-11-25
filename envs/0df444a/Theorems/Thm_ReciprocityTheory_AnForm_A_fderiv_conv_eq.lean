-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv_conv_eq
-- name    : ReciprocityTheory.AnForm.A.fderiv_conv_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:50:57.4382+00:00
-- url     : https://prove2.me/theorems/64bcb1f8-ae83-41d0-8cd9-06728ca2cf3a
-- title:
--   A: fderiv conv eq
-- statement:
--   The A construction uses the fderiv conv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L43-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L43-L48

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

theorem ReciprocityTheory.AnForm.A.fderiv_conv_eq {g : (ι → ℝ) → ℝ} (hg : Continuous g) :
    fderiv ℝ (convolution kK g (ContinuousLinearMap.lsmul ℝ ℝ) volume) =
      convolution (fderiv ℝ kK) g ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (ι → ℝ)) volume := by sorry
