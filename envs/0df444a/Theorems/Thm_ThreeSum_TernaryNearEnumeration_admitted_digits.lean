-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_digits
-- name    : ThreeSum.TernaryNearEnumeration.admitted_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:18.82361+00:00
-- url     : https://prove2.me/theorems/1a3c8b62-e38a-4bf0-83b3-ca7df44e9968
-- title:
--   Ternary Near Enumeration: admitted digits
-- statement:
--   The Ternary Near Enumeration construction uses the admitted digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L111-L122
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L111-L122

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses

theorem ThreeSum.TernaryNearEnumeration.admitted_digits {qs rs : List ℕ} {D : ℕ}
    (hq : ∀ q ∈ qs, q < 3) (h : Admitted qs rs D) : ∀ r ∈ rs, r < 3 := by sorry
