-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_eq_of_mem_31a5af5eaaf9
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_eq_of_mem_31a5af5eaaf9
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:44.309676+00:00
-- url     : https://prove2.me/theorems/15328e40-257b-4bfe-bce4-c906da76fc13
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq eq of mem 31a5af5eaaf9: P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq eq of mem 31a5af5eaaf9
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq eq of mem 31a5af5eaaf9 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq eq of mem 31a5af5eaaf9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L22-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L22-L39

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_eq_of_mem_31a5af5eaaf9 (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    ptNormSq W n s x = ‖s j x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ptNormSq_eq_of_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_eq_of_mem_31a5af5eaaf9
