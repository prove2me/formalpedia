-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_BoundedPshData_arg_contDiffAt_770a347dfdf8
-- name    : P2M_GroundTheory_Heights__Heights_Regular_BoundedPshData_arg_contDiffAt_770a347dfdf8
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:33:41.104005+00:00
-- url     : https://prove2.me/theorems/838bb2cf-500f-47b5-827d-19665184abbc
-- title:
--   P2 M Ground Theory Heights  Heights Regular Bounded Psh Data arg cont Diff At 770a347dfdf8: P2 M Ground Theory Heights  Heights Regular Bounded Psh Data arg cont Diff At 770a347dfdf8
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Bounded Psh Data arg cont Diff At 770a347dfdf8 construction uses the P2 M Ground Theory Heights  Heights Regular Bounded Psh Data arg cont Diff At 770a347dfdf8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedGlue.lean#L88-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PBoundedGlue.lean#L88-L103

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
open GroundTheory.Heights₂.Heights.Regular.BoundedPshData
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (B : BoundedPshData A)

theorem P2M_GroundTheory_Heights__Heights_Regular_BoundedPshData_arg_contDiffAt_770a347dfdf8 (ρ : Mollifier D) (η : Fin B.N → X → ℝ) {Cη t ε : ℝ}
    (hcut : B.IsCutoffFamily η Cη) (ht : 0 < t)
    (hball : ∀ j, ∀ x ∈ closure (B.mid j), closedBall (B.chart j x) t ⊆ (B.chart j).target)
    {ψ : OpenPartialHomeomorph X (Fin D → ℂ)} (hψ : IsCompatChart A ψ) {j : Fin B.N} {x : X}
    (hx : x ∈ ψ.source) (hj : x ∈ B.mid j) :
    ContDiffAt ℝ ∞ (fun y => B.phReg ρ t j (ψ.symm y) + 4 * ε * η j (ψ.symm y)) (ψ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«BoundedPshData».«arg_contDiffAt» := P2M_GroundTheory_Heights__Heights_Regular_BoundedPshData_arg_contDiffAt_770a347dfdf8
