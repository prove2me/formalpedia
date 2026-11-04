-- Prove2me | Theorems.Thm_ThreeSum_TernaryBankEnumeration_words_nodup
-- name    : ThreeSum.TernaryBankEnumeration.words_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:36:03.199775+00:00
-- url     : https://prove2.me/theorems/dcec3843-dd3c-40e5-831a-a9f1e7c4a485
-- title:
--   Ternary Bank Enumeration: words nodup
-- statement:
--   The Ternary Bank Enumeration construction uses the words nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L67-L70
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryBankEnumeration.lean#L67-L70

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryBank
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryEnumeration ThreeSum.TernaryAddresses
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryBankEnumeration.words_nodup (N T : ℕ) : (words N T).Nodup := by sorry
