-- Prove2me | Theorems.Thm_ThreeSum_TernaryCanonicalFibers_localBucket_length
-- name    : ThreeSum.TernaryCanonicalFibers.localBucket_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:38:30.704666+00:00
-- url     : https://prove2.me/theorems/29e7cffd-6776-424f-b941-3e91f18a4ee7
-- title:
--   Ternary Canonical Fibers: local Bucket length
-- statement:
--   The Ternary Canonical Fibers construction uses the local Bucket length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L64-L73
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalFibers.lean#L64-L73

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryCanonicalFibers.localBucket_length (p : ℤ) (raws : List ℤ) (x : ℤ) :
    (TernaryWantedRadix.localBucket p raws x).length=
      (raws.filter (fun z => p ∣ x-z)).length := by sorry
