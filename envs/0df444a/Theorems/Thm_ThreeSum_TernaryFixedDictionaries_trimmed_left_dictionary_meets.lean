-- Prove2me | Theorems.Thm_ThreeSum_TernaryFixedDictionaries_trimmed_left_dictionary_meets
-- name    : ThreeSum.TernaryFixedDictionaries.trimmed_left_dictionary_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:58:58.722431+00:00
-- url     : https://prove2.me/theorems/61b8db98-1b70-455c-9127-fdc371bc0aed
-- title:
--   Ternary Fixed Dictionaries: trimmed left dictionary meets
-- statement:
--   The Ternary Fixed Dictionaries construction uses the trimmed left dictionary meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L217-L234
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L217-L234

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

theorem ThreeSum.TernaryFixedDictionaries.trimmed_left_dictionary_meets (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) {base dst J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base+(trimmedLeftRecords (α := α) maps B).length ≤ dst)
    (hm : 0 < (trimmedLeftRecords (α := α) maps B).length)
    (hspace : LightRadixKeys.space dst (trimmedLeftRecords (α := α) maps B).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+1)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((trimmedLeftRecords (α := α) maps B).map (leftKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((trimmedLeftRecords (α := α) maps B).map (leftKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (trimmedLeftRecords (α := α) maps B).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (trimmedLeftRecords (α := α) maps B).length J)=
          (((trimmedLeftRecords (α := α) maps B).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (trimmedLeftRecords (α := α) maps B).length J+1)
          ((tuples (trimmedLeftRecords (α := α) maps B) J).map (Radix.positionalHash (p : ℤ) (leftKey maps))) ∧
        Kept μ ν base) := by sorry
