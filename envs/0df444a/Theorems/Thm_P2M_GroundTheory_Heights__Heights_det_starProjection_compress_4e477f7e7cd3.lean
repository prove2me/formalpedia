-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_starProjection_compress_4e477f7e7cd3
-- name    : P2M_GroundTheory_Heights__Heights_det_starProjection_compress_4e477f7e7cd3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:49:01.100196+00:00
-- url     : https://prove2.me/theorems/0d09f1f4-930d-596e-8d2b-393b15289ae9
-- title:
--   P2 M Ground Theory Heights  Heights det star Projection compress 4e477f7e7cd3: P2 M Ground Theory Heights  Heights det star Projection compress 4e477f7e7cd3
-- statement:
--   The P2 M Ground Theory Heights  Heights det star Projection compress 4e477f7e7cd3 construction uses the P2 M Ground Theory Heights  Heights det star Projection compress 4e477f7e7cd3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentJacCompress.lean#L11-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PTangentJacCompress.lean#L11-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTangentJacCompress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTangentJacCompress
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
open Module
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_det_starProjection_compress_4e477f7e7cd3 {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →L[ℂ] F) (T : Submodule ℂ E) :
    (T.starProjection ∘L A.adjoint ∘L A ∘L T.starProjection + (1 - T.starProjection)).det =
      (LinearMap.adjoint ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype) ∘ₗ ((A : E →ₗ[ℂ] F) ∘ₗ T.subtype)).det := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_starProjection_compress» := P2M_GroundTheory_Heights__Heights_det_starProjection_compress_4e477f7e7cd3
