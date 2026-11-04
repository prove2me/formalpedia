-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedModes_field_relation_iff
-- name    : ThreeSum.TernarySignedModes.field_relation_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:42:26.231965+00:00
-- url     : https://prove2.me/theorems/d4de987f-6c78-4e30-905f-05e09ac1912e
-- title:
--   Ternary Signed Modes: field relation iff
-- statement:
--   The Ternary Signed Modes construction uses the field relation iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L97-L108
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedModes.lean#L97-L108

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset

theorem ThreeSum.TernarySignedModes.field_relation_iff {p U radix J : ℕ} (hb : 1 < radix) (hp : 2*radix<p)
    (a b c : ℤ) (carry : CarryWord J) :
    (∀ k, fieldLeft p U radix J b k+fieldRight p U radix J c k=
      fieldRequester p U radix J a carry k) ↔
    (∀ k, leftRaw U radix J b k+rightRaw U radix J c k=requesterRaw U radix J a carry k) := by sorry
