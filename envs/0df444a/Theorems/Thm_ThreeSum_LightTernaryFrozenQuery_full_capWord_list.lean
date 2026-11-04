-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_full_capWord_list
-- name    : ThreeSum.LightTernaryFrozenQuery.full_capWord_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:28.097541+00:00
-- url     : https://prove2.me/theorems/18dc9a87-a3fa-4546-95e4-cdd725e3ddeb
-- title:
--   Light Ternary Frozen Query: full cap Word list
-- statement:
--   The Light Ternary Frozen Query construction uses the full cap Word list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L61-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryTime.lean#L61-L66

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryPrepare
import Definitions.Def_Submission_ThreeSum_TernaryFrozenQueryCost
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryFrozenQueryCost
set_option maxHeartbeats 3000000

theorem ThreeSum.LightTernaryFrozenQuery.full_capWord_list {N : ℕ} (R : TritWord N) :
    TernaryBankEnumeration.wordList (capWord (coords N N) R)=
      (TernaryBankEnumeration.wordList R).reverse := by sorry
