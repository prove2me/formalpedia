-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv2_regMax
-- name    : ReciprocityTheory.AnForm.A.fderiv2_regMax
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:55.852001+00:00
-- url     : https://prove2.me/theorems/a6a77605-6d02-4672-b755-a48b9c85e3b6
-- title:
--   A: fderiv2 reg Max
-- statement:
--   The A construction uses the fderiv2 reg Max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L115-L121

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

theorem ReciprocityTheory.AnForm.A.fderiv2_regMax {η : ℝ} (hη : 0 < η) (t : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) t =
      η⁻¹ • fderiv ℝ (fderiv ℝ (regMax (ι := ι) 1)) (η⁻¹ • t) := by sorry
