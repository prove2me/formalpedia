-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_smul_ab4f3601c209
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_smul_ab4f3601c209
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:20:17.043863+00:00
-- url     : https://prove2.me/theorems/61b891c5-0de6-458f-98c8-7a318ce457e2
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq smul ab4f3601c209: P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq smul ab4f3601c209
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq smul ab4f3601c209 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq smul ab4f3601c209 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L61-L64

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_smul_ab4f3601c209 (W : Weight L) (n : ℕ) (c : ℂ) (s : Fin A.n → X → ℂ) (x : X) :
    ptNormSq W n (c • s) x = ‖c‖ ^ 2 * ptNormSq W n s x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ptNormSq_smul» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_smul_ab4f3601c209
