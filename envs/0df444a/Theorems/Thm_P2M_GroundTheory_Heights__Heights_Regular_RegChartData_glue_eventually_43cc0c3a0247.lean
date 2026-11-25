-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_glue_eventually_43cc0c3a0247
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RegChartData_glue_eventually_43cc0c3a0247
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:35.53895+00:00
-- url     : https://prove2.me/theorems/5524b34c-06fb-4c10-9837-011d63a823ef
-- title:
--   P2 M Ground Theory Heights  Heights Regular Reg Chart Data glue eventually 43cc0c3a0247: P2 M Ground Theory Heights  Heights Regular Reg Chart Data glue eventually 43cc0c3a0247
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Reg Chart Data glue eventually 43cc0c3a0247 construction uses the P2 M Ground Theory Heights  Heights Regular Reg Chart Data glue eventually 43cc0c3a0247 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PGlueRegularised.lean#L24-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PGlueRegularised.lean#L24-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PGlueRegularised
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt regMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.RegChartData
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (R : RegChartData A)
open Classical

theorem P2M_GroundTheory_Heights__Heights_Regular_RegChartData_glue_eventually_43cc0c3a0247 (ρ : Mollifier D) (η : Fin R.N → X → ℝ) {Cη K t ε : ℝ}
    (hcut : R.IsCutoffFamily η Cη) (hε : 0 ≤ ε)
    (hcmp : ∀ j k, ∀ x ∈ R.mid j ∩ R.mid k, |R.phReg ρ K t j x - R.phReg ρ K t k x| ≤ ε)
    (x₀ : X) : ∀ᶠ y in 𝓝 x₀, (∀ j, x₀ ∈ R.mid j → y ∈ R.mid j) ∧
      R.regularised ρ K t ε η y =
        regMax ε (fun j : {j // x₀ ∈ R.mid j} => R.phReg ρ K t j y + 4 * ε * η j y) + ε / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RegChartData».«glue_eventually» := P2M_GroundTheory_Heights__Heights_Regular_RegChartData_glue_eventually_43cc0c3a0247
