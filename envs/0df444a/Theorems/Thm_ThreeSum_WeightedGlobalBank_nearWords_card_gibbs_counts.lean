-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalBank_nearWords_card_gibbs_counts
-- name    : ThreeSum.WeightedGlobalBank.nearWords_card_gibbs_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:16:45.145141+00:00
-- url     : https://prove2.me/theorems/ec7fa2b5-1580-48eb-bff0-68c89e0f645e
-- title:
--   Weighted Global Bank: near Words card gibbs counts
-- statement:
--   The Weighted Global Bank construction uses the near Words card gibbs counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L33-L38
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/GlobalBank.lean#L33-L38

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBank_nearWords_card_gibbs_counts

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalBank
open TernaryJointType

theorem ThreeSum.WeightedGlobalBank.nearWords_card_gibbs_counts {N : ℕ} (Q : TritWord N) (D : ℕ)
    (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (nearWords Q D).card*z^D≤(1+z^512)^digitCount Q 1*(1+z^513+z^1025)^digitCount Q 2 := by sorry
