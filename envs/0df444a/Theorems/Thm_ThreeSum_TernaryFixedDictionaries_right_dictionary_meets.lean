-- Prove2me | Theorems.Thm_ThreeSum_TernaryFixedDictionaries_right_dictionary_meets
-- name    : ThreeSum.TernaryFixedDictionaries.right_dictionary_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:58:50.516713+00:00
-- url     : https://prove2.me/theorems/57fb6e95-a1a3-434d-84d1-3212e5a62b09
-- title:
--   Ternary Fixed Dictionaries: right dictionary meets
-- statement:
--   The Ternary Fixed Dictionaries construction uses the right dictionary meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L177-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L177-L194

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

theorem ThreeSum.TernaryFixedDictionaries.right_dictionary_meets (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    {base dst J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base+(sourceRecords L α I).length ≤ dst)
    (hm : 0 < (sourceRecords L α I).length)
    (hspace : LightRadixKeys.space dst (sourceRecords L α I).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+1)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((sourceRecords L α I).map (rightKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((sourceRecords L α I).map (rightKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (sourceRecords L α I).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (sourceRecords L α I).length J)=
          (((sourceRecords L α I).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (sourceRecords L α I).length J+1)
          ((tuples (sourceRecords L α I) J).map (Radix.positionalHash (p : ℤ) (rightKey maps))) ∧
        Kept μ ν base) := by sorry
