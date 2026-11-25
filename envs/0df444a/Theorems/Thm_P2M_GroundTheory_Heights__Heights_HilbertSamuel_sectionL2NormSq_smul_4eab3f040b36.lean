-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_sectionL2NormSq_smul_4eab3f040b36
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_sectionL2NormSq_smul_4eab3f040b36
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:14:49.673544+00:00
-- url     : https://prove2.me/theorems/a4ebb29a-9807-4714-932d-92ddb2467357
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel section L2 Norm Sq smul 4eab3f040b36: P2 M Ground Theory Heights  Heights Hilbert Samuel section L2 Norm Sq smul 4eab3f040b36
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel section L2 Norm Sq smul 4eab3f040b36 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel section L2 Norm Sq smul 4eab3f040b36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/BergmanNorms.lean#L116-L119

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_sectionL2NormSq_smul_4eab3f040b36 (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (c : ℂ)
    (s : Fin A.n → X → ℂ) : sectionL2NormSq W dV n (c • s) = ‖c‖ ^ 2 * sectionL2NormSq W dV n s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«sectionL2NormSq_smul» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_sectionL2NormSq_smul_4eab3f040b36
