-- Prove2me | Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_wordList_capWord
-- name    : ThreeSum.WeightedFrozenQueryCost.wordList_capWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:15:21.390874+00:00
-- url     : https://prove2.me/theorems/4ec33b4c-6a60-44ea-8abe-950b17b31fcb
-- title:
--   Weighted Frozen Query Cost: word List cap Word
-- statement:
--   The Weighted Frozen Query Cost construction uses the word List cap Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L118-L120
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenQueryCost.lean#L118-L120

import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Theorems.Thm_ThreeSum_TernaryFrozenQueryCost_wordList_capWord

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedFrozenQueryCost
open Finset WeightedCache WeightedEnumeration

theorem ThreeSum.WeightedFrozenQueryCost.wordList_capWord {N : ℕ} (coords : List (Fin N)) (R : Word N) :
    WeightedBankEnumeration.wordList (capWord coords R)=caps coords R := by sorry
