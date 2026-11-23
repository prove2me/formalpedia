-- Prove2me | Theorems.Thm_P2M_Csg_idsCSG_stageGame_A__7bb1bc444f1d
-- name    : P2M_Csg_idsCSG_stageGame_A__7bb1bc444f1d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:50:47.551777+00:00
-- url     : https://prove2.me/theorems/c989d15c-d923-48ec-bd46-4e36aca70b04
-- title:
--   P2 M Csg ids CSG stage Game A  7bb1bc444f1d: P2 M Csg ids CSG stage Game A  7bb1bc444f1d
-- statement:
--   The stage-game payoff matrix against an arbitrary continuation `v`, generalising
--       `idsCSG_stageGame_A` (which only covers `v = fun _ => 0`).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L288-L294
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetection.lean#L288-L294

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
set_option autoImplicit true
open Csg

theorem P2M_Csg_idsCSG_stageGame_A__7bb1bc444f1d (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction)
    (v : IDSState → ℝ) :
    (idsCSG.stageGame s v).A a1 a2 = idsR s a1 a2 + v (idsNext a1 a2) := by sorry

alias «Csg».«idsCSG_stageGame_A'» := P2M_Csg_idsCSG_stageGame_A__7bb1bc444f1d
