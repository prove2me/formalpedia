-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalBank_rank_mono
-- name    : ThreeSum.WeightedGlobalBank.rank_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:16:38.841305+00:00
-- url     : https://prove2.me/theorems/2e3f8cc4-4b21-4b91-9f0d-27f363204241
-- title:
--   Weighted Global Bank: rank mono
-- statement:
--   The Weighted Global Bank construction uses the rank mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L23-L23
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L23-L23

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_rank_mono

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalBank
open TernaryJointType

theorem ThreeSum.WeightedGlobalBank.rank_mono {N : ℕ} {R Q : TritWord N} (h : Below R Q) : rank R≤rank Q := by sorry
