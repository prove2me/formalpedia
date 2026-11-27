-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_BoundedInjection_pos_fc12197aac5f
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_BoundedInjection_pos_fc12197aac5f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:14:13.364362+00:00
-- url     : https://prove2.me/theorems/d5d7f8ec-243c-4663-a3b8-1ddaed5d5455
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Bounded Injection pos fc12197aac5f: P2 M Ground Theory Heights  Heights Hilbert Samuel Bounded Injection pos fc12197aac5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Bounded Injection pos fc12197aac5f construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Bounded Injection pos fc12197aac5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/NormFibreVecPosOfLinearIndependent.lean#L26-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/NormFibreVecPosOfLinearIndependent.lean#L26-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StandardLatticeVecIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ShortFamilyEquivSmallFamilyVec
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_NormFibreVecPosOfLinearIndependent
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
open NumberField TensorProduct
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_BoundedInjection_pos_fc12197aac5f {E' E : HermitianBundle.{0} K} {A : (K →+* ℂ) → ℝ}
    (α : BoundedInjection E' E A) (h : 0 < bundleRank E') (σ : K →+* ℂ) : 0 < A σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«BoundedInjection».«pos» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_BoundedInjection_pos_fc12197aac5f
