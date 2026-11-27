-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ShortFamily_pos_e61eb3c36058
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ShortFamily_pos_e61eb3c36058
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:16:07.96343+00:00
-- url     : https://prove2.me/theorems/c3a83959-fa69-4a45-8650-bf38350d5229
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Short Family pos e61eb3c36058: P2 M Ground Theory Heights  Heights Hilbert Samuel Short Family pos e61eb3c36058
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Short Family pos e61eb3c36058 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Short Family pos e61eb3c36058 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/NormFibreVecPosOfLinearIndependent.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/NormFibreVecPosOfLinearIndependent.lean#L40-L45

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ShortFamily_pos_e61eb3c36058 {E : HermitianBundle.{0} K} {lam : (K →+* ℂ) → ℝ}
    (F : ShortFamily E lam) (h : 0 < bundleRank E) (σ : K →+* ℂ) : 0 < lam σ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ShortFamily».«pos» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ShortFamily_pos_e61eb3c36058
