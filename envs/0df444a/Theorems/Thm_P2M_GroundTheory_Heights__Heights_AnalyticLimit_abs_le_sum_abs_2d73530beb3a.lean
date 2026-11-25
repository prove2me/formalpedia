-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_le_sum_abs_2d73530beb3a
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_le_sum_abs_2d73530beb3a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:32:52.824902+00:00
-- url     : https://prove2.me/theorems/fa18fe5c-52e3-4f18-b081-489d80b085ad
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit abs le sum abs 2d73530beb3a: P2 M Ground Theory Heights  Heights Analytic Limit abs le sum abs 2d73530beb3a
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit abs le sum abs 2d73530beb3a construction uses the P2 M Ground Theory Heights  Heights Analytic Limit abs le sum abs 2d73530beb3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean#L148-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean#L148-L149

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
omit [Nonempty ι]

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_le_sum_abs_2d73530beb3a (a : ι → ℝ) (j : ι) : |a j| ≤ ∑ i, |a i| := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«abs_le_sum_abs» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_abs_le_sum_abs_2d73530beb3a
