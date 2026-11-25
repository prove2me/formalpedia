-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AddBlockBridge_scale_injective_d67dd2591a0b
-- name    : P2M_GroundTheory_Heights__Heights_AddBlockBridge_scale_injective_d67dd2591a0b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:16:49.717009+00:00
-- url     : https://prove2.me/theorems/97089113-001a-46f6-b5df-0f5d297db299
-- title:
--   P2 M Ground Theory Heights  Heights Add Block Bridge scale injective d67dd2591a0b: P2 M Ground Theory Heights  Heights Add Block Bridge scale injective d67dd2591a0b
-- statement:
--   The P2 M Ground Theory Heights  Heights Add Block Bridge scale injective d67dd2591a0b construction uses the P2 M Ground Theory Heights  Heights Add Block Bridge scale injective d67dd2591a0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L138-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PAddHeightsridge.lean#L138-L146

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_AddBlockBridge_scale_injective_d67dd2591a0b {σ L : Type} [Field L] (w : σ → L) (hw : ∀ o, w o ≠ 0) :
    Function.Injective (aeval fun o ↦ C (w o) * X o : MvPolynomial σ L →ₐ[L] MvPolynomial σ L) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AddBlockBridge».«scale_injective» := P2M_GroundTheory_Heights__Heights_AddBlockBridge_scale_injective_d67dd2591a0b
