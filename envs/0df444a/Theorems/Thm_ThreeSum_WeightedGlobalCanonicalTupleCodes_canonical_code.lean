-- Prove2me | Theorems.Thm_ThreeSum_WeightedGlobalCanonicalTupleCodes_canonical_code
-- name    : ThreeSum.WeightedGlobalCanonicalTupleCodes.canonical_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:09:16.563452+00:00
-- url     : https://prove2.me/theorems/cf1a9a8f-708d-403b-b906-58d21bb52f19
-- title:
--   Weighted Global Canonical Tuple Codes: canonical code
-- statement:
--   The Weighted Global Canonical Tuple Codes construction uses the canonical code property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalTupleCodes.lean#L28-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryCanonicalTupleCodes.lean#L28-L36

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryTupleWantedLookup
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalTupleCodes
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCanonicalTupleCodes
open TernaryJointType
set_option maxHeartbeats 2000000

theorem ThreeSum.WeightedGlobalCanonicalTupleCodes.canonical_code {A : Type*} {L r : ℕ} (word : A→TritWord L) (xs : Fin r→A) :
    Radix.positionalHash ((4^L : ℕ) : ℤ)
      (fun a => (TernaryCodeSemantics.address (word a) : ℤ)) (List.ofFn xs)=
      (TernaryCodeSemantics.address (WeightedGlobalRepeatedWords.canonical (word ∘ xs)) : ℤ) := by sorry
