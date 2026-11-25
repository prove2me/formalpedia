-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BallAverageLinear_matEquiv_apply_3bea487d655d
-- name    : P2M_GroundTheory_Heights__Heights_BallAverageLinear_matEquiv_apply_3bea487d655d
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:21.62065+00:00
-- url     : https://prove2.me/theorems/4a357371-2cb2-4602-85f0-328ba6639a98
-- title:
--   P2 M Ground Theory Heights  Heights Ball Average Linear mat Equiv apply 3bea487d655d: P2 M Ground Theory Heights  Heights Ball Average Linear mat Equiv apply 3bea487d655d
-- statement:
--   The P2 M Ground Theory Heights  Heights Ball Average Linear mat Equiv apply 3bea487d655d construction uses the P2 M Ground Theory Heights  Heights Ball Average Linear mat Equiv apply 3bea487d655d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PBallAverageLinear.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PBallAverageLinear.lean#L23-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PBallAverageLinear
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
open MeasureTheory Measure Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.BallAverageLinear

theorem P2M_GroundTheory_Heights__Heights_BallAverageLinear_matEquiv_apply_3bea487d655d {n : ℕ} (h : HermNorm n) (v : Fin n → ℂ) : matEquiv h v = h.mat *ᵥ v := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BallAverageLinear».«matEquiv_apply» := P2M_GroundTheory_Heights__Heights_BallAverageLinear_matEquiv_apply_3bea487d655d
