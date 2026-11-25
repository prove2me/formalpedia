-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_regMax_c2_pointwise_bound_0941e6435e3b
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_regMax_c2_pointwise_bound_0941e6435e3b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:32:36.564233+00:00
-- url     : https://prove2.me/theorems/6a0f68e1-27e9-4009-a9f2-3c65ca08384b
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit reg Max c2 pointwise bound 0941e6435e3b: P2 M Ground Theory Heights  Heights Analytic Limit reg Max c2 pointwise bound 0941e6435e3b
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit reg Max c2 pointwise bound 0941e6435e3b construction uses the P2 M Ground Theory Heights  Heights Analytic Limit reg Max c2 pointwise bound 0941e6435e3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean#L151-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean#L151-L266

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
import Theorems.Thm_ReciprocityTheory_AnForm_A_abs_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv2_regMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_add_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_comp_fderiv2
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_sum
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_fderiv2_bound
import Theorems.Thm_ReciprocityTheory_AnForm_A_two_le_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax regMax_contDiff regMax_add_const abs_regMax_le regMax_fderiv_sum
  regMax_fderiv_nonneg fderiv2_regMax regMax_one_fderiv2_bound regMax_comp_fderiv2 two_le_inf)
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι] [Nonempty ι]

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_regMax_c2_pointwise_bound_0941e6435e3b {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ContDiffOn ℝ 2 f U)
    {u : ι → E → ℝ} (hu : ∀ j, ContDiffOn ℝ 2 (u j) U) {η : ℝ} (hη : 0 < η) {C : ℝ}
    (hC : ∀ p : ι → ℝ, ‖fderiv ℝ (fderiv ℝ (regMax (ι := ι) η)) p‖ ≤ C / η) {z : E} (hz : z ∈ U)
    {s0 s1 s2 : ℝ} (h0 : ∀ j, |u j z - f z| ≤ s0)
    (h1 : ∀ j, ‖fderiv ℝ (u j) z - fderiv ℝ f z‖ ≤ s1)
    (h2 : ∀ j, ‖fderiv ℝ (fderiv ℝ (u j)) z - fderiv ℝ (fderiv ℝ f) z‖ ≤ s2) :
    |(regMax η (fun j => u j z) + η / 2) - f z| ≤ s0 + η ∧
      ‖fderiv ℝ (fun x => regMax η (fun j => u j x) + η / 2) z - fderiv ℝ f z‖ ≤ s1 ∧
      ‖fderiv ℝ (fderiv ℝ (fun x => regMax η (fun j => u j x) + η / 2)) z -
          fderiv ℝ (fderiv ℝ f) z‖ ≤ 2 * (C / η * s1 ^ 2 + s2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«regMax_c2_pointwise_bound» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_regMax_c2_pointwise_bound_0941e6435e3b
