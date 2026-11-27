-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tendstoC2On_chart_symm_compact_0f368e5618d9
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tendstoC2On_chart_symm_compact_0f368e5618d9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:14.663263+00:00
-- url     : https://prove2.me/theorems/b7e5f195-4980-587b-8cd5-2ba4761eec09
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit System tendsto C2 On chart symm compact 0f368e5618d9: P2 M Ground Theory Heights  Heights Analytic Limit System tendsto C2 On chart symm compact 0f36
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit System tendsto C2 On chart symm compact 0f368e5618d9 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit System tendsto C2 On chart symm compact 0f368e5618d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean#L331-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean#L331-L334

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
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} {R : RegChartData A}

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tendstoC2On_chart_symm_compact_0f368e5618d9 (S : System R) (k : Fin A.n) {K : Set (Fin D → ℂ)} (hK : IsCompact K)
    (hKs : K ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' R.Yo) :
    TendstoC2On (fun t y => S.ph t ((A.chart k).symm y)) (fun y => R.φ ((A.chart k).symm y)) K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«System».«tendstoC2On_chart_symm_compact» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_System_tendstoC2On_chart_symm_compact_0f368e5618d9
