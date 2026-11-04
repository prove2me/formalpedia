-- Prove2me | Theorems.Thm_ThreeSum_TernaryCanonicalDictionaries_native_bound
-- name    : ThreeSum.TernaryCanonicalDictionaries.native_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:01:55.129469+00:00
-- url     : https://prove2.me/theorems/6c5db39b-4eca-4e7e-af30-a3172778e7d8
-- title:
--   Ternary Canonical Dictionaries: native bound
-- statement:
--   The Ternary Canonical Dictionaries construction uses the native bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalDictionaries.lean#L35-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalDictionaries.lean#L35-L39

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

theorem ThreeSum.TernaryCanonicalDictionaries.native_bound (right : Bool) (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : |native right maps r| ≤ (p : ℤ) := by sorry
