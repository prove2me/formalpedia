-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_globalKey_outputOfChoices
-- name    : ThreeSum.GlobalEncoding.globalKey_outputOfChoices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:12:58.487398+00:00
-- url     : https://prove2.me/theorems/b4867c43-4962-4948-b5b9-a6409319a029
-- title:
--   Global Encoding: global Key output Of Choices
-- statement:
--   The exact, unreduced global hash difference depends only on the
--   occurrence/output tuple, and hence is independent of every internal split.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L272-L277
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L272-L277

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments

theorem ThreeSum.GlobalEncoding.globalKey_outputOfChoices {h J : ℕ} (xs : List (RetainedChoice h))
    (hlen : xs.length = J) :
    globalKey (outputOfChoices xs hlen) =
      Radix.positionalHash (localPrime h) rawRight xs -
        Radix.positionalHash (localPrime h) rawLeft xs := by sorry
