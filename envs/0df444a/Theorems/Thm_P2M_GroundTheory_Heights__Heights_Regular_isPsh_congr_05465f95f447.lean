-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_isPsh_congr_05465f95f447
-- name    : P2M_GroundTheory_Heights__Heights_Regular_isPsh_congr_05465f95f447
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:24.161794+00:00
-- url     : https://prove2.me/theorems/3da1f0c7-8d70-4f1c-80e5-fa9e38152c4e
-- title:
--   P2 M Ground Theory Heights  Heights Regular is Psh congr 05465f95f447: P2 M Ground Theory Heights  Heights Regular is Psh congr 05465f95f447
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular is Psh congr 05465f95f447 construction uses the P2 M Ground Theory Heights  Heights Regular is Psh congr 05465f95f447 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L85-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/GlueCharts.lean#L85-L97

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

theorem P2M_GroundTheory_Heights__Heights_Regular_isPsh_congr_05465f95f447 {U : Set (Fin D → ℂ)} {φ ψ : (Fin D → ℂ) → ℝ} (h : EqOn φ ψ U)
    (hφ : IsPsh U φ) : IsPsh U ψ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«isPsh_congr» := P2M_GroundTheory_Heights__Heights_Regular_isPsh_congr_05465f95f447
