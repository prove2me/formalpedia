-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_digitCount_wordList
-- name    : ThreeSum.LightTernaryFrozenQuery.digitCount_wordList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:30.120872+00:00
-- url     : https://prove2.me/theorems/01871464-92fc-4c22-b49b-a32743b55f86
-- title:
--   Light Ternary Frozen Query: digit Count word List
-- statement:
--   The Light Ternary Frozen Query construction uses the digit Count word List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L56-L59
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L56-L59

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryFrozenQueryCost
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryFrozenQuery.digitCount_wordList {N : ℕ} (R : TritWord N) (d : Fin 3) :
    digitCount R d=((TernaryBankEnumeration.wordList R).map
      (fun a : ℕ => if a=d.val then 1 else 0)).sum := by sorry
