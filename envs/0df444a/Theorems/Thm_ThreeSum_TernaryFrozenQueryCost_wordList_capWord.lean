-- Prove2me | Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_wordList_capWord
-- name    : ThreeSum.TernaryFrozenQueryCost.wordList_capWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:11:13.292752+00:00
-- url     : https://prove2.me/theorems/1e1f06e5-3af8-4392-89ca-46431eb39a02
-- title:
--   Ternary Frozen Query Cost: word List cap Word
-- statement:
--   The Ternary Frozen Query Cost construction uses the word List cap Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L98-L100
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFrozenQueryCost.lean#L98-L100

import Definitions.Def_Submission_ThreeSum_TernaryReconstruction
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryFrozenQueryCost
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryQuery
set_option maxHeartbeats 2000000

theorem ThreeSum.TernaryFrozenQueryCost.wordList_capWord {N : ℕ} (coords : List (Fin N)) (R : TritWord N) :
    TernaryBankEnumeration.wordList (capWord coords R)=caps coords R := by sorry
