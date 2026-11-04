-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCanonicalTupleCodes_digit_cast
-- name    : ThreeSum.WeightedGlobalCanonicalTupleCodes.digit_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:12:02.823195+00:00
-- url     : https://prove2.me/theorems/2ef056a8-5672-489b-810b-9619714e8beb
-- title:
--   Weighted Global Canonical Tuple Codes: digit cast
-- statement:
--   The Weighted Global Canonical Tuple Codes construction uses the digit cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalTupleCodes.lean#L38-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalTupleCodes.lean#L38-L44

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleWantedLookup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCanonicalTupleCodes
open TernaryJointType
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalCanonicalTupleCodes.digit_cast (R : ℕ) {A : Type*} (raw : A→ℕ) (xs : List A) :
    Radix.positionalHash (R : ℤ) (fun a => (raw a : ℤ)) xs=
      ((Nat.ofDigits R (xs.map raw) : ℕ) : ℤ) := by sorry
