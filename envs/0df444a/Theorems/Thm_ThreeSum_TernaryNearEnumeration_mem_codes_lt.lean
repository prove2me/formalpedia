-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_codes_lt
-- name    : ThreeSum.TernaryNearEnumeration.mem_codes_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:21.490206+00:00
-- url     : https://prove2.me/theorems/4d0276fa-5caa-4077-aece-518afd54f676
-- title:
--   Ternary Near Enumeration: mem codes lt
-- statement:
--   The Ternary Near Enumeration construction uses the mem codes lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L146-L151
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L146-L151

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryAddresses_mem_codes_lt

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses

theorem ThreeSum.TernaryNearEnumeration.mem_codes_lt {qs : List ℕ} {D a : ℕ}
    (hq : ∀ q ∈ qs, q < 3) (ha : a ∈ codes qs D) : a < 4^qs.length := by sorry
