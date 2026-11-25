-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_SmoothVolume_isOpenPosMeasure_239f6b264a4a
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_SmoothVolume_isOpenPosMeasure_239f6b264a4a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:41.686678+00:00
-- url     : https://prove2.me/theorems/e17570a3-e78b-586d-8dad-2b501ffbf75a
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Smooth Volume is Open Pos Measure 239f6b264a4a: P2 M Ground Theory Heights  Heights Hilbert Samuel Smooth Volume is Open Pos Measure 239f6b264a4a
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Smooth Volume is Open Pos Measure 239f6b264a4a construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Smooth Volume is Open Pos Measure 239f6b264a4a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L68-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L68-L101

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_SmoothVolume_isOpenPosMeasure_239f6b264a4a (dV : SmoothVolume A) : dV.μ.IsOpenPosMeasure := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«SmoothVolume».«isOpenPosMeasure» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_SmoothVolume_isOpenPosMeasure_239f6b264a4a
