-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverLocal_rawPairCount_le_rawCap
-- name    : ThreeSum.TernaryCoverLocal.rawPairCount_le_rawCap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:47:13.877223+00:00
-- url     : https://prove2.me/theorems/2be6800c-bd74-4b51-b918-7979c7396a78
-- title:
--   Ternary Cover Local: raw Pair Count le raw Cap
-- statement:
--   The Ternary Cover Local construction uses the raw Pair Count le raw Cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L185-L193
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverLocal.lean#L185-L193

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

theorem ThreeSum.TernaryCoverLocal.rawPairCount_le_rawCap (α π : DigitType)
    (w : Coordinate (Fin L) → ZMod p) (a b : ZMod p) :
    TernaryCoverFibers.rawPairCount (leftHash (α := α) (π := π) w) (rightHash w) a b ≤
      rawCap α π w := by sorry
