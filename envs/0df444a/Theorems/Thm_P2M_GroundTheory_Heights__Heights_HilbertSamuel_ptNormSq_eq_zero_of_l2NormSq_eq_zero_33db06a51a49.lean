-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_eq_zero_of_l2NormSq_eq_zero_33db06a51a49
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_eq_zero_of_l2NormSq_eq_zero_33db06a51a49
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:15:37.994141+00:00
-- url     : https://prove2.me/theorems/87a24594-d95b-5073-8eb3-db02a7f4e192
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq eq zero of l2 Norm Sq eq zero 33db06a51a49: P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq eq zero of l2 Norm Sq eq zero 33
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq eq zero of l2 Norm Sq eq zero 33db06a51a49 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel pt Norm Sq eq zero of l2 Norm Sq eq zero 33db06a51a49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L121-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L121-L128

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_eq_zero_of_l2NormSq_eq_zero_33db06a51a49 (W : Weight L) (dV : SmoothVolume A) [CompactSpace X]
    {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) (h0 : sectionL2NormSq W dV n s = 0) (x : X) :
    ptNormSq W n s x = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ptNormSq_eq_zero_of_l2NormSq_eq_zero» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_eq_zero_of_l2NormSq_eq_zero_33db06a51a49
