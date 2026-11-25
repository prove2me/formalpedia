-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_dist_lt_iff_norm_sub_73d8e6366e39
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_dist_lt_iff_norm_sub_73d8e6366e39
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:31:02.563647+00:00
-- url     : https://prove2.me/theorems/b9dde935-8776-5d68-955e-0855d6a005b3
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit dist lt iff norm sub 73d8e6366e39: P2 M Ground Theory Heights  Heights Analytic Limit dist lt iff norm sub 73d8e6366e39
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit dist lt iff norm sub 73d8e6366e39 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit dist lt iff norm sub 73d8e6366e39 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean#L89-L91

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_dist_lt_iff_norm_sub_73d8e6366e39 {F : Type*} [SeminormedAddCommGroup F] {a b : F} {e : ℝ} :
    dist a b < e ↔ ‖b - a‖ < e := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«dist_lt_iff_norm_sub» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_dist_lt_iff_norm_sub_73d8e6366e39
