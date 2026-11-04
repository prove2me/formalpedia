-- Prove2me | Theorems.Thm_ThreeSum_TernaryFixedDictionaries_source_choice_keys
-- name    : ThreeSum.TernaryFixedDictionaries.source_choice_keys
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:58:37.885473+00:00
-- url     : https://prove2.me/theorems/6d87c190-c835-4fa4-9d44-dcdf2578744f
-- title:
--   Ternary Fixed Dictionaries: source choice keys
-- statement:
--   Actual sourcekey membership retains occurrence IDs separately from integer labels.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L53-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L53-L60

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryFixedDictionaries.source_choice_keys {Ω : Type*} (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (occ : Ω → I) (edge : Ω → LocalEdge L α π) (c : Ω) :
    ∃ rL rR : SourceRecord L α I,
      rL ∈ sourceRecords L α I ∧ rR ∈ sourceRecords L α I ∧
      leftKey maps rL = rawLeft maps occ edge c ∧ rightKey maps rR = rawRight maps occ edge c := by sorry
