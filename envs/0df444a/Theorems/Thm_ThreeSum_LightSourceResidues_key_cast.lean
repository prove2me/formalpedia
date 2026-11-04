-- Prove2me | Theorems.Thm_ThreeSum_LightSourceResidues_key_cast
-- name    : ThreeSum.LightSourceResidues.key_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:31:35.501558+00:00
-- url     : https://prove2.me/theorems/23387479-0f70-49eb-a5ef-c770d06c2608
-- title:
--   Light Source Residues: key cast
-- statement:
--   The Light Source Residues construction uses the key cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceResidues.lean#L20-L22
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightSourceResidues.lean#L20-L22

import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceResidues
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

theorem ThreeSum.LightSourceResidues.key_cast {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by sorry
