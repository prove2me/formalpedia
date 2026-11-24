-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_analyticAt_comp_symm_of_holoOn_7994d19dece0
-- name    : P2M_GroundTheory_Heights__Heights_Regular_analyticAt_comp_symm_of_holoOn_7994d19dece0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:50.763926+00:00
-- url     : https://prove2.me/theorems/2f814b1d-8891-4177-b808-bb51f5e5ebd7
-- title:
--   P2 M Ground Theory Heights  Heights Regular analytic At comp symm of holo On 7994d19dece0: P2 M Ground Theory Heights  Heights Regular analytic At comp symm of holo On 7994d19dece0
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular analytic At comp symm of holo On 7994d19dece0 construction uses the P2 M Ground Theory Heights  Heights Regular analytic At comp symm of holo On 7994d19dece0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L76-L81

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

theorem P2M_GroundTheory_Heights__Heights_Regular_analyticAt_comp_symm_of_holoOn_7994d19dece0 (hψ : IsCompatChart A ψ) {W : Set X}
    {G : X → ℂ} (hG : A.HoloOn W G) {x : X} (hxW : x ∈ W) (hx : x ∈ ψ.source) :
    AnalyticAt ℂ (G ∘ ψ.symm) (ψ x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«analyticAt_comp_symm_of_holoOn» := P2M_GroundTheory_Heights__Heights_Regular_analyticAt_comp_symm_of_holoOn_7994d19dece0
