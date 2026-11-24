-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_comp_fderiv2
-- name    : ReciprocityTheory.AnForm.A.regMax_comp_fderiv2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:51.641696+00:00
-- url     : https://prove2.me/theorems/8b8d1c7e-3f5c-474d-a4bd-8010b82112c0
-- title:
--   A: reg Max comp fderiv2
-- statement:
--   The A construction uses the reg Max comp fderiv2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L245-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshRegMax.lean#L245-L276

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem ReciprocityTheory.AnForm.A.regMax_comp_fderiv2 {η : ℝ} (hη : 0 < η) {U : Set E} (hU : IsOpen U)
    {u : ι → E → ℝ} (hu : ∀ j, ContDiffOn ℝ 2 (u j) U) {z : E} (hz : z ∈ U) (v : E) :
    fderiv ℝ (fderiv ℝ (fun x => regMax η (fun j => u j x))) z v v =
      fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) (fun j => u j z) (fun j => fderiv ℝ (u j) z v)
          (fun j => fderiv ℝ (u j) z v) +
        fderiv ℝ (regMax (ι := ι) η) (fun j => u j z) (fun j => fderiv ℝ (fderiv ℝ (u j)) z v v) := by sorry
