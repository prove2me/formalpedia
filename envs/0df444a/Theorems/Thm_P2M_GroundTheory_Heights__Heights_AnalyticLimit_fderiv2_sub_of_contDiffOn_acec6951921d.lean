-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_sub_of_contDiffOn_acec6951921d
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_sub_of_contDiffOn_acec6951921d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:39:05.541118+00:00
-- url     : https://prove2.me/theorems/1c735106-f544-4064-8f84-863f7cd17bd8
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit fderiv2 sub of cont Diff On acec6951921d: P2 M Ground Theory Heights  Heights Analytic Limit fderiv2 sub of cont Diff On acec6951921d
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit fderiv2 sub of cont Diff On acec6951921d construction uses the P2 M Ground Theory Heights  Heights Analytic Limit fderiv2 sub of cont Diff On acec6951921d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean#L74-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean#L74-L87

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_sub_of_contDiffOn_acec6951921d {U : Set E} (hU : IsOpen U) {φ ψ : E → ℝ}
    (hφ : ContDiffOn ℝ 2 φ U) (hψ : ContDiffOn ℝ 2 ψ U) {x : E} (hx : x ∈ U) :
    fderiv ℝ (fderiv ℝ fun y => φ y - ψ y) x =
      fderiv ℝ (fderiv ℝ φ) x - fderiv ℝ (fderiv ℝ ψ) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«fderiv2_sub_of_contDiffOn» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_fderiv2_sub_of_contDiffOn_acec6951921d
