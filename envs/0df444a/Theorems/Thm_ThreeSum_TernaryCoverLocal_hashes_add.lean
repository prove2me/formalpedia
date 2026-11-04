-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_hashes_add
-- name    : ThreeSum.TernaryCoverLocal.hashes_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:47:17.477838+00:00
-- url     : https://prove2.me/theorems/743fa182-d65f-4468-87c0-ea709b9d5a56
-- title:
--   Ternary Cover Local: hashes add
-- statement:
--   The Ternary Cover Local construction uses the hashes add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L112-L121
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L112-L121

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
variable [Fact (Nat.Prime p)]

theorem ThreeSum.TernaryCoverLocal.hashes_add {α π : DigitType} (w : Coordinate (Fin L) → ZMod p)
    (e : LocalEdge L α π) : leftHash w e + rightHash w e = outputHash w (output e) := by sorry
