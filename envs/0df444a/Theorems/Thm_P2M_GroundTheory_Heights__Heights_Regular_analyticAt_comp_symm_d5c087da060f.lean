-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_analyticAt_comp_symm_d5c087da060f
-- name    : P2M_GroundTheory_Heights__Heights_Regular_analyticAt_comp_symm_d5c087da060f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:00.298379+00:00
-- url     : https://prove2.me/theorems/32f74d28-578c-4b05-af1b-ee5dbf1cfb31
-- title:
--   P2 M Ground Theory Heights  Heights Regular analytic At comp symm d5c087da060f: P2 M Ground Theory Heights  Heights Regular analytic At comp symm d5c087da060f
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular analytic At comp symm d5c087da060f construction uses the P2 M Ground Theory Heights  Heights Regular analytic At comp symm d5c087da060f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L37-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L37-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
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
open ReciprocityTheory.AnForm.A (IsPsh Mollifier molli coordDiv limsupExt shrink)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm (levi)
noncomputable section
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X}
variable {ψ : OpenPartialHomeomorph X (Fin D → ℂ)}

theorem P2M_GroundTheory_Heights__Heights_Regular_analyticAt_comp_symm_d5c087da060f {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (hψ : IsCompatChart A ψ) {g : X → E} {x : X} (hx : x ∈ ψ.source) (i : Fin A.n)
    (hxi : x ∈ (A.chart i).source) (hg : AnalyticAt ℂ (g ∘ (A.chart i).symm) (A.chart i x)) :
    AnalyticAt ℂ (g ∘ ψ.symm) (ψ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«analyticAt_comp_symm» := P2M_GroundTheory_Heights__Heights_Regular_analyticAt_comp_symm_d5c087da060f
