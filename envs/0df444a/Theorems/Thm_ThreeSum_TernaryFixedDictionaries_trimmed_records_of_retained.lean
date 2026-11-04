-- Prove2me | Theorems.Thm_ThreeSum_TernaryFixedDictionaries_trimmed_records_of_retained
-- name    : ThreeSum.TernaryFixedDictionaries.trimmed_records_of_retained
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:58:32.229935+00:00
-- url     : https://prove2.me/theorems/4bdef722-0b81-4ed6-ad7b-550d5d8b6785
-- title:
--   Ternary Fixed Dictionaries: trimmed records of retained
-- statement:
--   The Ternary Fixed Dictionaries construction uses the trimmed records of retained property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L91-L105
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L91-L105

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryFixedDictionaries.trimmed_records_of_retained {Ω : Type*}
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    (occ : Ω → I) (edge : Ω → LocalEdge L α π) (c : Ω)
    (hleft : TernaryCoverTrimming.bucketSize (fieldVertices L p α) TernaryCoverHashes.leftVector
      (maps (occ c)) (leftHash (maps (occ c)) (edge c)) ≤ B)
    (hright : TernaryCoverTrimming.bucketSize (fieldVertices L p α) TernaryCoverHashes.rightVector
      (maps (occ c)) (rightHash (maps (occ c)) (edge c)) ≤ B) :
    ∃ rL rR : SourceRecord L α I,
      rL ∈ trimmedLeftRecords maps B ∧ rR ∈ trimmedRightRecords maps B ∧
      leftKey maps rL = rawLeft maps occ edge c ∧ rightKey maps rR = rawRight maps occ edge c := by sorry
