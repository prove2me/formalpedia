-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_glue_eventually_of_close_bb9fb9720f63
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_glue_eventually_of_close_bb9fb9720f63
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:33:43.971845+00:00
-- url     : https://prove2.me/theorems/2cb197a1-1481-4f2e-86be-5a671135ce34
-- title:
--   P2 M Ground Theory Heights  Heights Regular Potential Charts glue eventually of close bb9fb9720f63: P2 M Ground Theory Heights  Heights Regular Potential Charts glue eventually of close bb9fb9720f63
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Potential Charts glue eventually of close bb9fb9720f63 construction uses the P2 M Ground Theory Heights  Heights Regular Potential Charts glue eventually of close bb9fb9720f63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedGlue.lean#L25-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedGlue.lean#L25-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_RegMaxReindex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedGlue
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
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli regMax shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_add_smul levi_re_analytic)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PotentialCharts
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)
open Classical

theorem P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_glue_eventually_of_close_bb9fb9720f63 (a : Fin P.N → X → ℝ) (η : Fin P.N → X → ℝ) {Cη ε : ℝ}
    (hcut : P.IsCutoffFamily η Cη) (hε : 0 ≤ ε)
    (hcmp : ∀ j k, ∀ x ∈ P.mid j ∩ P.mid k, |a j x - a k x| ≤ ε)
    (x₀ : X) : ∀ᶠ y in 𝓝 x₀, (∀ j, x₀ ∈ P.mid j → y ∈ P.mid j) ∧
      P.glue (fun j x => a j x + 4 * ε * η j x) ε y =
        regMax ε (fun j : {j // x₀ ∈ P.mid j} => a j y + 4 * ε * η j y) + ε / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PotentialCharts».«glue_eventually_of_close» := P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_glue_eventually_of_close_bb9fb9720f63
