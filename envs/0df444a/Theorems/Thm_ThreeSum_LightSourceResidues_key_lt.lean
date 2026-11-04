-- Prove2me | Theorems.Thm_ThreeSum_LightSourceResidues_key_lt
-- name    : ThreeSum.LightSourceResidues.key_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:27:57.423872+00:00
-- url     : https://prove2.me/theorems/710f6d64-0fa0-47f7-9bee-6ce879828804
-- title:
--   Light Source Residues: key lt
-- statement:
--   The Light Source Residues construction uses the key lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceResidues.lean#L24-L28
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceResidues.lean#L24-L28

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceResidues
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

theorem ThreeSum.LightSourceResidues.key_lt {p m : ℕ} (hm : 0 < m) (shift x : ℤ) : key p m shift x < m := by sorry
