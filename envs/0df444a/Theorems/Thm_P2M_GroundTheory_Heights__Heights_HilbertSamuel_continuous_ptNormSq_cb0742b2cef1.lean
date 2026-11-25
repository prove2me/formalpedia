-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuous_ptNormSq_cb0742b2cef1
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuous_ptNormSq_cb0742b2cef1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:24:48.081889+00:00
-- url     : https://prove2.me/theorems/d332e46c-0a6f-4320-8f55-4cb43d37bab6
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel continuous pt Norm Sq cb0742b2cef1: P2 M Ground Theory Heights  Heights Hilbert Samuel continuous pt Norm Sq cb0742b2cef1
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel continuous pt Norm Sq cb0742b2cef1 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel continuous pt Norm Sq cb0742b2cef1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L45-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L45-L59

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuous_ptNormSq_cb0742b2cef1 (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) : Continuous (ptNormSq W n s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«continuous_ptNormSq» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuous_ptNormSq_cb0742b2cef1
