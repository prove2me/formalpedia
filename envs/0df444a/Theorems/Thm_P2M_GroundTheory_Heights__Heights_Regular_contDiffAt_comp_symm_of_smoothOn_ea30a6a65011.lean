-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_contDiffAt_comp_symm_of_smoothOn_ea30a6a65011
-- name    : P2M_GroundTheory_Heights__Heights_Regular_contDiffAt_comp_symm_of_smoothOn_ea30a6a65011
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:43.693576+00:00
-- url     : https://prove2.me/theorems/f45cdcb9-9669-46a4-bb97-1e3984a810c4
-- title:
--   P2 M Ground Theory Heights  Heights Regular cont Diff At comp symm of smooth On ea30a6a65011: P2 M Ground Theory Heights  Heights Regular cont Diff At comp symm of smooth On ea30a6a65011
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular cont Diff At comp symm of smooth On ea30a6a65011 construction uses the P2 M Ground Theory Heights  Heights Regular cont Diff At comp symm of smooth On ea30a6a65011 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L63-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L63-L74

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

theorem P2M_GroundTheory_Heights__Heights_Regular_contDiffAt_comp_symm_of_smoothOn_ea30a6a65011 (hψ : IsCompatChart A ψ) {U : Set X} (hU : IsOpen U)
    {f : X → ℝ} (hf : A.SmoothOn U f) {x : X} (hxU : x ∈ U) (hx : x ∈ ψ.source) :
    ContDiffAt ℝ ∞ (f ∘ ψ.symm) (ψ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«contDiffAt_comp_symm_of_smoothOn» := P2M_GroundTheory_Heights__Heights_Regular_contDiffAt_comp_symm_of_smoothOn_ea30a6a65011
