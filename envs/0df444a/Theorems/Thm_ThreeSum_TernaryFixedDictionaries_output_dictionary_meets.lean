-- Prove2me | Theorems.Thm_ThreeSum_TernaryFixedDictionaries_output_dictionary_meets
-- name    : ThreeSum.TernaryFixedDictionaries.output_dictionary_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:58:55.840523+00:00
-- url     : https://prove2.me/theorems/5ad3b94d-66e2-433e-b3d1-ab6f38e743fd
-- title:
--   Ternary Fixed Dictionaries: output dictionary meets
-- statement:
--   The Ternary Fixed Dictionaries construction uses the output dictionary meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L197-L214
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryFixedDictionaries.lean#L197-L214

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

theorem ThreeSum.TernaryFixedDictionaries.output_dictionary_meets (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    {base dst J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase : base+(outputRecords L π I).length ≤ dst)
    (hm : 0 < (outputRecords L π I).length)
    (hspace : LightRadixKeys.space dst (outputRecords L π I).length J ≤ lim.space)
    (hword : (LightRadixKeys.word p ((2*L+2)*p) J : ℤ) ≤ lim.word)
    (hd : d+J+3 ≤ lim.depth) :
    Meets lim (LightFixedRadixDictionary.program ((outputRecords L π I).map (blockKey maps)))
      4 d [base,dst,J,p] μ (LightFixedRadixDictionary.time ((outputRecords L π I).map (blockKey maps)) J)
      (fun r ν => r=((dst+LightRadixKeys.offset (outputRecords L π I).length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset (outputRecords L π I).length J)=
          (((outputRecords L π I).length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset (outputRecords L π I).length J+1)
          ((tuples (outputRecords L π I) J).map (Radix.positionalHash (p : ℤ) (blockKey maps))) ∧
        Kept μ ν base) := by sorry
