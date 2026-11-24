-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_nonneg_d0797495dc03
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_nonneg_d0797495dc03
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:24:47.638804+00:00
-- url     : https://prove2.me/theorems/20cc4ea9-0cbb-455a-a1ac-b4070ae3a3bf
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq nonneg d0797495dc03: P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq nonneg d0797495dc03
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq nonneg d0797495dc03 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq nonneg d0797495dc03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L41-L43

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_nonneg_d0797495dc03 (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    0 ≤ ptNormSq W n s x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ptNormSq_nonneg» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_nonneg_d0797495dc03
