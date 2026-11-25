-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_levi_lower_bound_of_isCompact_bb98515e5025
-- name    : P2M_GroundTheory_Heights__Heights_Regular_levi_lower_bound_of_isCompact_bb98515e5025
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:18:38.640285+00:00
-- url     : https://prove2.me/theorems/38edf1cd-1407-4984-bf6d-7961357555d2
-- title:
--   P2 M Ground Theory Heights  Heights Regular levi lower bound of is Compact bb98515e5025: P2 M Ground Theory Heights  Heights Regular levi lower bound of is Compact bb98515e5025
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular levi lower bound of is Compact bb98515e5025 construction uses the P2 M Ground Theory Heights  Heights Regular levi lower bound of is Compact bb98515e5025 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PCutoffs.lean#L33-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PCutoffs.lean#L33-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PCutoffs
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_chartPush_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_contDiffOn_compat
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_isCompact_symm_image
import Theorems.Thm_ReciprocityTheory_AnForm_M_PLAux_smooth_chartPush

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
open Metric Set Filter Topology
open scoped ContDiff Manifold
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (chartPush chartPush_eq_zero isCompact_symm_image smooth_chartPush
  contDiffOn_compat)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_levi_lower_bound_of_isCompact_bb98515e5025 {D : ℕ} {f : (Fin D → ℂ) → ℝ} {U K : Set (Fin D → ℂ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ w, -C * ‖w‖ ^ 2 ≤ levi f y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«levi_lower_bound_of_isCompact» := P2M_GroundTheory_Heights__Heights_Regular_levi_lower_bound_of_isCompact_bb98515e5025
