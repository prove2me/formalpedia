-- Prove2me | Theorems.Thm_ThreeSum_TernaryWeightChannels_powerCircuit_eval
-- name    : ThreeSum.TernaryWeightChannels.powerCircuit_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:40:18.23347+00:00
-- url     : https://prove2.me/theorems/42208147-65a9-4c03-a138-2b8043f7fc7b
-- title:
--   Ternary Weight Channels: power Circuit eval
-- statement:
--   The Ternary Weight Channels construction uses the power Circuit eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean#L13-L17
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryWeightChannels.lean#L13-L17

import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWeightChannels
open Finset LightFixedArithmetic TernaryJointType TernaryWeightedPhysicalSources
open scoped BigOperators

theorem ThreeSum.TernaryWeightChannels.powerCircuit_eval (e : Circuit) (k : ℕ) (x : ℕ→ℤ) :
    (powerCircuit e k).eval x=(e.eval x)^k := by sorry
