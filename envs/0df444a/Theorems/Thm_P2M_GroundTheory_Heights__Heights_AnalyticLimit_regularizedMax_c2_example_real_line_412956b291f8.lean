-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_regularizedMax_c2_example_real_line_412956b291f8
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_regularizedMax_c2_example_real_line_412956b291f8
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:32:09.10133+00:00
-- url     : https://prove2.me/theorems/45a96789-dfc7-4eb9-8023-9e3b1334ecfc
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit regularized Max c2 example real line 412956b291f8: P2 M Ground Theory Heights  Heights Analytic Limit regularized Max c2 example real line 412956b291
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit regularized Max c2 example real line 412956b291f8 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit regularized Max c2 example real line 412956b291f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean#L338-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean#L338-L363

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_regularizedMax_c2_example_real_line_412956b291f8 :
    TendstoC2On (fun t x => regMax t (fun j : Fin 2 => x ^ 2 + ((j : ℕ) : ℝ) * t) + t / 2)
      (fun x : ℝ => x ^ 2) (Set.Icc (-1) 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«regularizedMax_c2_example_real_line» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_regularizedMax_c2_example_real_line_412956b291f8
