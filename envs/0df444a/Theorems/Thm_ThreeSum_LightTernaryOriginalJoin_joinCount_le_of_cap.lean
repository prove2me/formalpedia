-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryOriginalJoin_joinCount_le_of_cap
-- name    : ThreeSum.LightTernaryOriginalJoin.joinCount_le_of_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:39.068495+00:00
-- url     : https://prove2.me/theorems/2cf32627-445f-4294-8bbd-5469dc5debb0
-- title:
--   Light Ternary Original Join: join Count le of cap
-- statement:
--   The Light Ternary Original Join construction uses the join Count le of cap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryOriginalJoin.lean#L30-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryOriginalJoin.lean#L30-L44

import Definitions.Def_Submission_ThreeSum_LightWantedSetup
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LightTernaryOriginalJoin
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryOriginalJoin
open Light
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000

theorem ThreeSum.LightTernaryOriginalJoin.joinCount_le_of_cap {M NL cap : ℕ} {input : ℕ → ℤ}
    {p : ℤ} {base : List ℤ} {J : ℕ} {shift : ℤ}
    (hcap : ∀ i < NL,
      LightHistogram.count
        (fun j => WantedResidueKeys.code M 0 ((keys p base J).getD j 0))
        (WantedResidueKeys.code M shift (input i)) (keys p base J).length ≤ cap) :
    joinCount M input NL p base J shift ≤ NL*cap := by sorry
