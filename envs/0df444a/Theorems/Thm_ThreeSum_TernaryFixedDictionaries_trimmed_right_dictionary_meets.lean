-- Prove2me | Theorems.Thm_ThreeSum_TernaryFixedDictionaries_trimmed_right_dictionary_meets
-- name    : ThreeSum.TernaryFixedDictionaries.trimmed_right_dictionary_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:59:29.329802+00:00
-- url     : https://prove2.me/theorems/c63a419c-a6d6-47c8-99af-b9872e782c87
-- title:
--   Ternary Fixed Dictionaries: trimmed right dictionary meets
-- statement:
--   The Ternary Fixed Dictionaries construction uses the trimmed right dictionary meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L236-L253
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L236-L253

import Definitions.Def_Submission_ThreeSum_TernaryGlobalEncoding
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryFixedDictionaries
open Finset TernaryJointType TernaryCoverLocal TernaryGlobalEncoding RadixKeyLists Light
variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {lim : Limits}

theorem ThreeSum.TernaryFixedDictionaries.trimmed_right_dictionary_meets (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) {base dst J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base+(trimmedRightRecords (α := α) maps B).length ≤ dst)
    (hm : 0 < (trimmedRightRecords (α := α) maps B).length)
    (hspace : LightRadixKeys.space dst (trimmedRightRecords (α := α) maps B).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+1)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((trimmedRightRecords (α := α) maps B).map (rightKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((trimmedRightRecords (α := α) maps B).map (rightKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (trimmedRightRecords (α := α) maps B).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (trimmedRightRecords (α := α) maps B).length J)=
          (((trimmedRightRecords (α := α) maps B).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (trimmedRightRecords (α := α) maps B).length J+1)
          ((tuples (trimmedRightRecords (α := α) maps B) J).map (Radix.positionalHash (p : ℤ) (rightKey maps))) ∧
        Kept μ ν base) := by sorry
