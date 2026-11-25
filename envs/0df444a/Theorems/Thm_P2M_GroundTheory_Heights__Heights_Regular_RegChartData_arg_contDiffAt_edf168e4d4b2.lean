-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_arg_contDiffAt_edf168e4d4b2
-- name    : P2M_GroundTheory_Heights__Heights_Regular_RegChartData_arg_contDiffAt_edf168e4d4b2
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:33:40.190804+00:00
-- url     : https://prove2.me/theorems/6b514bc2-5469-5f29-a2c0-8160572f4624
-- title:
--   P2 M Ground Theory Heights  Heights Regular Reg Chart Data arg cont Diff At edf168e4d4b2: P2 M Ground Theory Heights  Heights Regular Reg Chart Data arg cont Diff At edf168e4d4b2
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Reg Chart Data arg cont Diff At edf168e4d4b2 construction uses the P2 M Ground Theory Heights  Heights Regular Reg Chart Data arg cont Diff At edf168e4d4b2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PGlueRegularised.lean#L66-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PGlueRegularised.lean#L66-L81

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

theorem P2M_GroundTheory_Heights__Heights_Regular_RegChartData_arg_contDiffAt_edf168e4d4b2 (ρ : Mollifier D) (η : Fin R.N → X → ℝ) {Cη K t ε : ℝ}
    (hcut : R.IsCutoffFamily η Cη) (ht : 0 < t)
    (hball : ∀ j, ∀ x ∈ closure (R.mid j), closedBall (R.chart j x) t ⊆ (R.chart j).target)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {j : Fin R.N} {x : X}
    (hx : x ∈ ψ.source) (hj : x ∈ R.mid j) :
    ContDiffAt ℝ ∞ (fun y => R.phReg ρ K t j (ψ.symm y) + 4 * ε * η j (ψ.symm y)) (ψ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«RegChartData».«arg_contDiffAt» := P2M_GroundTheory_Heights__Heights_Regular_RegChartData_arg_contDiffAt_edf168e4d4b2
