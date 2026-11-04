-- Prove2me | Theorems.Thm_ThreeSum_LightSourceResidues_time_bound
-- name    : ThreeSum.LightSourceResidues.time_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:27:39.718354+00:00
-- url     : https://prove2.me/theorems/d765b215-20ea-4fca-8078-0eafbb9c4f80
-- title:
--   Light Source Residues: time bound
-- statement:
--   The Light Source Residues construction uses the time bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceResidues.lean#L161-L165
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceResidues.lean#L161-L165

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceResidues
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightSourceResidues.time_bound (n p U D : ℕ) :
    time n p U D ≤
      254*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+6 := by sorry
