-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_eq_nearWords_card
-- name    : ThreeSum.TernaryNearBankEnumeration.codes_length_eq_nearWords_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:38:14.321261+00:00
-- url     : https://prove2.me/theorems/4fb77eb0-4b77-4bfb-9d4e-d45ad812f989
-- title:
--   Ternary Near Bank Enumeration: codes length eq near Words card
-- statement:
--   The Ternary Near Bank Enumeration construction uses the codes length eq near Words card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L62-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearBankEnumeration.lean#L62-L67

import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Mathlib.Data.List.Forall2
import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearBankEnumeration
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration

theorem ThreeSum.TernaryNearBankEnumeration.codes_length_eq_nearWords_card {N : ℕ} (Q : TritWord N) (D : ℕ) :
    (TernaryNearEnumeration.codes (wordList Q) D).length = (nearWords Q D).card := by sorry
