-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradDensSheetBound_abs_le_of_forall_pos_19b8f3740a14
-- name    : P2M_GroundTheory_Heights__Heights_GradDensSheetBound_abs_le_of_forall_pos_19b8f3740a14
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:19:37.789516+00:00
-- url     : https://prove2.me/theorems/b5bb470b-9bfd-4c04-bb47-8b3145fd6985
-- title:
--   P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound abs le of forall pos 19b8f3740a14: P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound abs le of forall pos 19b8f3740a14
-- statement:
--   The P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound abs le of forall pos 19b8f3740a14 construction uses the P2 M Ground Theory Heights  Heights Grad Dens Sheet Bound abs le of forall pos 19b8f3740a14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L97-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGradDensSheetBound.lean#L97-L136

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffBoundaryParts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGradDensSheetBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.GradDensSheetBound

theorem P2M_GroundTheory_Heights__Heights_GradDensSheetBound_abs_le_of_forall_pos_19b8f3740a14 {X P Q K : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hK : 0 ≤ K)
    (h : ∀ u : ℝ, 0 < u → 2 * |X| ≤ K * (u * P + u⁻¹ * Q)) :
    |X| ≤ K * Real.sqrt P * Real.sqrt Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GradDensSheetBound».«abs_le_of_forall_pos» := P2M_GroundTheory_Heights__Heights_GradDensSheetBound_abs_le_of_forall_pos_19b8f3740a14
