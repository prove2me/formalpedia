-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_BallAverageLinear_ballH_eq_preimage_917609adca6c
-- name    : P2M_GroundTheory_Heights__Heights_BallAverageLinear_ballH_eq_preimage_917609adca6c
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:20.453926+00:00
-- url     : https://prove2.me/theorems/1b4e2877-0d8c-48b5-aee5-b930160fc3a5
-- title:
--   P2 M Ground Theory Heights  Heights Ball Average Linear ball H eq preimage 917609adca6c: P2 M Ground Theory Heights  Heights Ball Average Linear ball H eq preimage 917609adca6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Ball Average Linear ball H eq preimage 917609adca6c construction uses the P2 M Ground Theory Heights  Heights Ball Average Linear ball H eq preimage 917609adca6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PBallAverageLinear.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PBallAverageLinear.lean#L25-L28

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

theorem P2M_GroundTheory_Heights__Heights_BallAverageLinear_ballH_eq_preimage_917609adca6c {n : ℕ} (h : HermNorm n) :
    ballH h = matEquiv h ⁻¹' ballH (HermNorm.std n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«BallAverageLinear».«ballH_eq_preimage» := P2M_GroundTheory_Heights__Heights_BallAverageLinear_ballH_eq_preimage_917609adca6c
