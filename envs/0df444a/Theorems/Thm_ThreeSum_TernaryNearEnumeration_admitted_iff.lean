-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_iff
-- name    : ThreeSum.TernaryNearEnumeration.admitted_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:14.060824+00:00
-- url     : https://prove2.me/theorems/c627d327-a831-4082-84e0-0dd092285523
-- title:
--   Ternary Near Enumeration: admitted iff
-- statement:
--   The Ternary Near Enumeration construction uses the admitted iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L91-L109
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L91-L109

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses

theorem ThreeSum.TernaryNearEnumeration.admitted_iff (qs rs : List ℕ) (D : ℕ) :
    Admitted qs rs D ↔ List.Forall₂ (· ≤ ·) rs qs ∧
      (List.zipWith Nat.sub qs rs).sum ≤ D := by sorry
