-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexCharP_finite_subring_fb0d73c5f47f
-- name    : P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexCharP_finite_subring_fb0d73c5f47f
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:34.822272+00:00
-- url     : https://prove2.me/theorems/528b33f0-d7d9-427d-9731-c62ca8885a9e
-- title:
--   P2 M Ground Theory Heights  Heights Targets Invertible Index Char P finite subring fb0d73c5f47f: P2 M Ground Theory Heights  Heights Targets Invertible Index Char P finite subring fb0d73c5f47f
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Invertible Index Char P finite subring fb0d73c5f47f construction uses the P2 M Ground Theory Heights  Heights Targets Invertible Index Char P finite subring fb0d73c5f47f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleIndexCharP.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PInvertibleIndexCharP.lean#L9-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsInvertibleIndexMulSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PInvertibleIndexCharP
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
open GroundTheory.Heights₂.Heights

theorem P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexCharP_finite_subring_fb0d73c5f47f {Ω : Type} [Field Ω] (B : Subring Ω) (hp : ringChar Ω ≠ 0)
    (hB : Module.Finite ℤ B) : Finite B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«InvertibleIndexCharP».«finite_subring» := P2M_GroundTheory_Heights__Heights_Targets_InvertibleIndexCharP_finite_subring_fb0d73c5f47f
