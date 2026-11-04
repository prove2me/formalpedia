-- Prove2me | Theorems.Thm_ThreeSum_TernarySignedReduction_tagged_relation_iff
-- name    : ThreeSum.TernarySignedReduction.tagged_relation_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:37:54.186514+00:00
-- url     : https://prove2.me/theorems/81fc1de5-e782-47cb-9402-48dab930a611
-- title:
--   Ternary Signed Reduction: tagged relation iff
-- statement:
--   The Ternary Signed Reduction construction uses the tagged relation iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L88-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernarySignedReduction.lean#L88-L102

import Definitions.Def_Submission_ThreeSum_TernarySignedDigits
import Mathlib.Data.ZMod.Basic
import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset

theorem ThreeSum.TernarySignedReduction.tagged_relation_iff (U radix J : ℕ) (a b c : ℤ) (carry : CarryWord J) :
    (∀ k, leftRaw U radix J b k+rightRaw U radix J c k=requesterRaw U radix J a carry k) ↔
      DigitRelation radix J (shiftOne U b) (shiftOne U a) (shiftTwo U c) carry := by sorry
