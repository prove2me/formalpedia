-- Prove2me | Theorems.Thm_ThreeSum_TernaryCanonicalDictionaries_records_length_le
-- name    : ThreeSum.TernaryCanonicalDictionaries.records_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:02:42.251498+00:00
-- url     : https://prove2.me/theorems/f5704bb0-fdcf-472d-96a8-498b1a288a44
-- title:
--   Ternary Canonical Dictionaries: records length le
-- statement:
--   The Ternary Canonical Dictionaries construction uses the records length le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalDictionaries.lean#L16-L24
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalDictionaries.lean#L16-L24

import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalDictionaries
open Finset Light RadixKeyLists TernaryFixedDictionaries TernaryJointType
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem ThreeSum.TernaryCanonicalDictionaries.records_length_le (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ) :
    (records (α := α) right maps B).length ≤ Fintype.card I*(TernaryCoverLocal.vertices L α).card := by sorry
