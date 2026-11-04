-- Prove2me | Theorems.Thm_ThreeSum_GlobalEncoding_globalOutput_card
-- name    : ThreeSum.GlobalEncoding.globalOutput_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:48:26.00983+00:00
-- url     : https://prove2.me/theorems/0754b4c2-ad83-4a1b-8d35-42bca64db993
-- title:
--   Global Encoding: global Output card
-- statement:
--   The Global Encoding construction uses the global Output card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L241-L244
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalEncoding.lean#L241-L244

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

theorem ThreeSum.GlobalEncoding.globalOutput_card (h J : ℕ) :
    Fintype.card (GlobalOutput h J) =
      scheduleSize h ^ J * outputCount (512 * h) h ^ J := by sorry
