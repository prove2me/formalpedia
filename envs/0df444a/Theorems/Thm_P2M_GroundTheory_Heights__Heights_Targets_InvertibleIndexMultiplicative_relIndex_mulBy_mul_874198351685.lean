-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_relIndex_mulBy_mul_874198351685
-- name    : P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_relIndex_mulBy_mul_874198351685
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:32.506859+00:00
-- url     : https://prove2.me/theorems/d51cacc4-4b66-5e0d-844c-27471c61bc6a
-- title:
--   P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative rel Index mul By mul 874198351685: P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative rel Index mul
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative rel Index mul By mul 874198351685 construction uses the P2 M Ground Theory Heights  Heights Targets Invertible Index Multiplicative rel Index mul By mul 874198351685 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleIndexMul.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleIndexMul.lean#L31-L45

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

theorem P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_relIndex_mulBy_mul_874198351685 {B : Subring Ω} {x y : Ω} (hx : x ≠ 0) (hxB : x ∈ B) (hyB : y ∈ B) :
    (B.toAddSubgroup.map (mulBy (x * y))).relIndex B.toAddSubgroup =
      (B.toAddSubgroup.map (mulBy x)).relIndex B.toAddSubgroup *
        (B.toAddSubgroup.map (mulBy y)).relIndex B.toAddSubgroup := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«InvertibleIndexMultiplicative».«relIndex_mulBy_mul» := P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexMultiplicative_relIndex_mulBy_mul_874198351685
