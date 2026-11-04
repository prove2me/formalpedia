-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalBank_cost_add_deficit
-- name    : ThreeSum.WeightedGlobalBank.cost_add_deficit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:16:33.167775+00:00
-- url     : https://prove2.me/theorems/3fa7072b-ac18-4d55-936f-e9d773c05f8c
-- title:
--   Weighted Global Bank: cost add deficit
-- statement:
--   The Weighted Global Bank construction uses the cost add deficit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L24-L26
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L24-L26

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_GlobalBank
import Theorems.Thm_WeightedCache_cost_add_deficit

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalBank
open TernaryJointType

theorem ThreeSum.WeightedGlobalBank.cost_add_deficit {N : ℕ} {R Q : TritWord N} (h : Below R Q) :
    cacheCost R+deficit Q R=cacheCost Q := by sorry
