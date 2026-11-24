-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_comp_symm_eventuallyEq_0d3f4d850af4
-- name    : P2M_GroundTheory_Heights__Heights_Regular_comp_symm_eventuallyEq_0d3f4d850af4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:05.996251+00:00
-- url     : https://prove2.me/theorems/e5461a40-c60a-457a-a486-239b96c8e85c
-- title:
--   P2 M Ground Theory Heights  Heights Regular comp symm eventually Eq 0d3f4d850af4: P2 M Ground Theory Heights  Heights Regular comp symm eventually Eq 0d3f4d850af4
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular comp symm eventually Eq 0d3f4d850af4 construction uses the P2 M Ground Theory Heights  Heights Regular comp symm eventually Eq 0d3f4d850af4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L24-L31

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

theorem P2M_GroundTheory_Heights__Heights_Regular_comp_symm_eventuallyEq_0d3f4d850af4 {E : Type*} (g : X → E) {x : X} (hx : x ∈ ψ.source) (i : Fin A.n)
    (hxi : x ∈ (A.chart i).source) :
    (g ∘ (A.chart i).symm) ∘ (A.chart i ∘ ψ.symm) =ᶠ[𝓝 (ψ x)] g ∘ ψ.symm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«comp_symm_eventuallyEq» := P2M_GroundTheory_Heights__Heights_Regular_comp_symm_eventuallyEq_0d3f4d850af4
