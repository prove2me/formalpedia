-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GraphAreaIntegral_continuous_areaJacobian_da03433f263c
-- name    : P2M_GroundTheory_Heights__Heights_GraphAreaIntegral_continuous_areaJacobian_da03433f263c
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:05.941798+00:00
-- url     : https://prove2.me/theorems/45e49e20-7003-4ce2-a66f-ab7696e0f9d2
-- title:
--   P2 M Ground Theory Heights  Heights Graph Area Integral continuous area Jacobian da03433f263c: P2 M Ground Theory Heights  Heights Graph Area Integral continuous area Jacobian da03433f263c
-- statement:
--   The P2 M Ground Theory Heights  Heights Graph Area Integral continuous area Jacobian da03433f263c construction uses the P2 M Ground Theory Heights  Heights Graph Area Integral continuous area Jacobian da03433f263c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGraphAreaIntegral.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PGraphAreaIntegral.lean#L14-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsGraphAreaFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PGraphAreaIntegral
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
open MeasureTheory
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_GraphAreaIntegral_continuous_areaJacobian_da03433f263c {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] :
    Continuous fun M : E →L[ℝ] F => areaJacobian (M : E →ₗ[ℝ] F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GraphAreaIntegral».«continuous_areaJacobian» := P2M_GroundTheory_Heights__Heights_GraphAreaIntegral_continuous_areaJacobian_da03433f263c
