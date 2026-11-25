-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_integrable_ptNormSq_c8a0c94a85ca
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_integrable_ptNormSq_c8a0c94a85ca
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:02.255191+00:00
-- url     : https://prove2.me/theorems/7625dc68-2786-49dc-bfe5-acbfe31e8b64
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel integrable pt Norm Sq c8a0c94a85ca: P2 M Ground Theory Heights  Heights Hilbert Samuel integrable pt Norm Sq c8a0c94a85ca
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel integrable pt Norm Sq c8a0c94a85ca construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel integrable pt Norm Sq c8a0c94a85ca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L103-L107

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_integrable_ptNormSq_c8a0c94a85ca (W : Weight L) (dV : SmoothVolume A) [CompactSpace X] {n : ℕ}
    {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) : Integrable (ptNormSq W n s) dV.μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«integrable_ptNormSq» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_integrable_ptNormSq_c8a0c94a85ca
