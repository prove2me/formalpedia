-- Prove2me | Theorems.Thm_ThreeSum_TernaryNearEnumeration_admitted_deficit
-- name    : ThreeSum.TernaryNearEnumeration.admitted_deficit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:34:13.312769+00:00
-- url     : https://prove2.me/theorems/b240093f-9709-4275-a4c2-1bc5f249f62a
-- title:
--   Ternary Near Enumeration: admitted deficit
-- statement:
--   The Ternary Near Enumeration construction uses the admitted deficit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L77-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryNearEnumeration.lean#L77-L89

import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearEnumeration
open ThreeSum.TernaryAddresses

theorem ThreeSum.TernaryNearEnumeration.admitted_deficit {qs rs : List ℕ} {D : ℕ} (h : Admitted qs rs D) :
    (List.zipWith Nat.sub qs rs).sum ≤ D := by sorry
