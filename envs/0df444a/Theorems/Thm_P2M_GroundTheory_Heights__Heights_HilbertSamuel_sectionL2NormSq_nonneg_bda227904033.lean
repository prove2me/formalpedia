-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_sectionL2NormSq_nonneg_bda227904033
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_sectionL2NormSq_nonneg_bda227904033
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:15:19.600912+00:00
-- url     : https://prove2.me/theorems/a9cba049-78e1-44dc-92cd-dd34b0a1babe
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel section L2 Norm Sq nonneg bda227904033: P2 M Ground Theory Heights  Heights Hilbert Samuel section L2 Norm Sq nonneg bda227904033
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel section L2 Norm Sq nonneg bda227904033 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel section L2 Norm Sq nonneg bda227904033 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L110-L112

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanNorms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}
variable [MeasurableSpace X] [BorelSpace X]
omit [BorelSpace X]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_sectionL2NormSq_nonneg_bda227904033 (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (s : Fin A.n → X → ℂ) :
    0 ≤ sectionL2NormSq W dV n s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«sectionL2NormSq_nonneg» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_sectionL2NormSq_nonneg_bda227904033
