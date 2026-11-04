-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearEnumeration_words_nodup
-- name    : ThreeSum.TernaryNearEnumeration.words_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:23.662216+00:00
-- url     : https://prove2.me/theorems/651d9cb3-7378-4702-80ac-a3624086cc77
-- title:
--   Ternary Near Enumeration: words nodup
-- statement:
--   The Ternary Near Enumeration construction uses the words nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L177-L181
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L177-L181

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses

theorem ThreeSum.TernaryNearEnumeration.words_nodup (qs : List ℕ) (D : ℕ) (hq : ∀ q ∈ qs, q < 3) :
    (words qs D).Nodup := by sorry
