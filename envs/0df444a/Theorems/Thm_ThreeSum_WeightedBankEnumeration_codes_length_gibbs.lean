-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankEnumeration_codes_length_gibbs
-- name    : ThreeSum.WeightedBankEnumeration.codes_length_gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:44.50929+00:00
-- url     : https://prove2.me/theorems/2e7ffe81-e014-478c-969e-e7b19abb42ed
-- title:
--   Weighted Bank Enumeration: codes length gibbs
-- statement:
--   The Weighted Bank Enumeration construction uses the codes length gibbs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L92-L96
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L92-L96

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType

theorem ThreeSum.WeightedBankEnumeration.codes_length_gibbs (N T : ℕ) (y : ℝ) (hy : 0≤y) (hy1 : y≤1) :
    (codes N T).length*y^T ≤ (1+y^512+y^1025)^N := by sorry
