-- Prove2me | Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
-- name    : ThreeSum.LightFixedRadixDictionary.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:48:06.553195+00:00
-- url     : https://prove2.me/theorems/c589f6cd-6821-4269-83d3-1eff7f0494bd
-- title:
--   Light Fixed Radix Dictionary: program meets
-- statement:
--   The Light Fixed Radix Dictionary construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedRadixDictionary.lean#L21-L49
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedRadixDictionary.lean#L21-L49

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightFixedRadixDictionary
open Light RadixKeyLists
variable {lim : Limits}
set_option maxHeartbeats 1400000

theorem ThreeSum.LightFixedRadixDictionary.program_meets (xs : List ℤ) {base dst p U J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hbase : base+xs.length ≤ dst)
    (hm : 0 < xs.length) (hbound : ∀ x ∈ xs, |x| ≤ (U : ℤ))
    (hspace : LightRadixKeys.space dst xs.length J ≤ lim.space)
    (hword : (LightRadixKeys.word p U J : ℤ) ≤ lim.word) (hd : d+J+3 ≤ lim.depth) :
    Meets lim (program xs) 4 d [base,dst,J,p] μ (time xs J)
      (fun r ν => r=((dst+LightRadixKeys.offset xs.length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset xs.length J)=((xs.length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset xs.length J+1) (values (p : ℤ) xs J) ∧
        Kept μ ν base) := by sorry
