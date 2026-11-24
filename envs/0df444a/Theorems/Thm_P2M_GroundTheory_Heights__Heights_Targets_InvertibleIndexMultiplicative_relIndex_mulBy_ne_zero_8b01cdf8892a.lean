-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_relIndex_mulBy_ne_zero_8b01cdf8892a
-- name    : P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_relIndex_mulBy_ne_zero_8b01cdf8892a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:31.149795+00:00
-- url     : https://prove2.me/theorems/4ce184da-a84f-4136-bcfc-6b82d78b5115
-- title:
--   P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative rel Index mul By ne zero 8b01cdf8892a: P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative rel Index
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative rel Index mul By ne zero 8b01cdf8892a construction uses the P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative rel Index mul By ne zero 8b01cdf8892a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleIndexMul.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleIndexMul.lean#L26-L29

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

theorem P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_relIndex_mulBy_ne_zero_8b01cdf8892a [CharZero Ω] {B : Subring Ω} [Module.Finite ℤ B] {β : B} (hβ : β ≠ 0) :
    (B.toAddSubgroup.map (mulBy (β : Ω))).relIndex B.toAddSubgroup ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«InvertibleIndexMultiplicative».«relIndex_mulBy_ne_zero» := P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_relIndex_mulBy_ne_zero_8b01cdf8892a
