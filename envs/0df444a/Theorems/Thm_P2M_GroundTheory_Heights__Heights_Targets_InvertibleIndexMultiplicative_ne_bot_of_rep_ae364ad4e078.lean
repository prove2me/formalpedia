-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_ne_bot_of_rep_ae364ad4e078
-- name    : P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_ne_bot_of_rep_ae364ad4e078
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:05.13009+00:00
-- url     : https://prove2.me/theorems/6ec598eb-0aa7-5ae1-807a-069e4f55aad0
-- title:
--   P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative ne bot of rep ae364ad4e078: P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative ne bot of rep ae364a
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative ne bot of rep ae364ad4e078 construction uses the P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative ne bot of rep ae364ad4e078 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleIndexMul.lean#L47-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleIndexMul.lean#L47-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleIndexMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open GroundTheory.Heights₂.Heights InvertibleIdealIndexAlt
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.InvertibleIndexMultiplicative
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_ne_bot_of_rep_ae364ad4e078 {B : Subring Ω} {X : AddSubgroup Ω} {β δ : B} {I : Ideal B} (hβ : β ≠ 0)
    (hX0 : X ≠ ⊥) (hX : ∀ x, x ∈ X ↔ ∃ y ∈ I, (β : Ω) * x = δ * y) : I ≠ ⊥ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«InvertibleIndexMultiplicative».«ne_bot_of_rep» := P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_ne_bot_of_rep_ae364ad4e078
