-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearEnumeration_mem_digits
-- name    : ThreeSum.TernaryNearEnumeration.mem_digits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:08.51305+00:00
-- url     : https://prove2.me/theorems/f01ff462-375d-41da-b172-b28496917562
-- title:
--   Ternary Near Enumeration: mem digits
-- statement:
--   The Ternary Near Enumeration construction uses the mem digits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L18-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L18-L20

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses

theorem ThreeSum.TernaryNearEnumeration.mem_digits {q D r : ℕ} :
    r ∈ digits q D ↔ r ≤ q ∧ q-r ≤ D := by sorry
