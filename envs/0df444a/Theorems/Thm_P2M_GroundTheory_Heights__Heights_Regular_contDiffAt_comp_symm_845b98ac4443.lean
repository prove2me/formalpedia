-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_contDiffAt_comp_symm_845b98ac4443
-- name    : P2M_GroundTheory_Heights__Heights_Regular_contDiffAt_comp_symm_845b98ac4443
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:25.394589+00:00
-- url     : https://prove2.me/theorems/351aa836-b5e6-4530-9098-b5f72dd2b08c
-- title:
--   P2 M Ground Theory Heights  Heights Regular cont Diff At comp symm 845b98ac4443: P2 M Ground Theory Heights  Heights Regular cont Diff At comp symm 845b98ac4443
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular cont Diff At comp symm 845b98ac4443 construction uses the P2 M Ground Theory Heights  Heights Regular cont Diff At comp symm 845b98ac4443 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L46-L54

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

theorem P2M_GroundTheory_Heights__Heights_Regular_contDiffAt_comp_symm_845b98ac4443 (hψ : IsCompatChart A ψ) {n : WithTop ℕ∞} {g : X → ℝ} {x : X}
    (hx : x ∈ ψ.source) (i : Fin A.n) (hxi : x ∈ (A.chart i).source)
    (hg : ContDiffAt ℝ n (g ∘ (A.chart i).symm) (A.chart i x)) :
    ContDiffAt ℝ n (g ∘ ψ.symm) (ψ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«contDiffAt_comp_symm» := P2M_GroundTheory_Heights__Heights_Regular_contDiffAt_comp_symm_845b98ac4443
