-- Prove2me | Theorems.Thm_ThreeSum_WeightedBankEnumeration_digitCost_eq
-- name    : ThreeSum.WeightedBankEnumeration.digitCost_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:35:37.731202+00:00
-- url     : https://prove2.me/theorems/67fd15bf-c949-44ac-b976-7393609742a2
-- title:
--   Weighted Bank Enumeration: digit Cost eq
-- statement:
--   The Weighted Bank Enumeration construction uses the digit Cost eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L23-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/BankEnumeration.lean#L23-L24

import Definitions.Def_Submission_Weighted_Addresses
import Definitions.Def_Submission_Weighted_Cache
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_Weighted_BankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.WeightedBankEnumeration
open ThreeSum.WeightedEnumeration ThreeSum.WeightedAddresses
open ThreeSum.TernaryJointType

theorem ThreeSum.WeightedBankEnumeration.digitCost_eq (d : Fin 3) : digitCost d.val = (![0,512,1025] : Fin 3→ℕ) d := by sorry
