-- Prove2me | Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets_records
-- name    : ThreeSum.LightFixedRadixDictionary.program_meets_records
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:38:57.480683+00:00
-- url     : https://prove2.me/theorems/09c699fe-e4df-45b2-945c-cae4bb7cb851
-- title:
--   Light Fixed Radix Dictionary: program meets records
-- statement:
--   The array's records remain in literal tuple order even when keys agree.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedRadixDictionary.lean#L52-L66
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightFixedRadixDictionary.lean#L52-L66

import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Definitions.Def_Submission_ThreeSum_LightRadixKeys
import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
set_option autoImplicit false
open ThreeSum ThreeSum.LightFixedRadixDictionary
open Light RadixKeyLists
variable {lim : Limits}
set_option maxHeartbeats 1400000

theorem ThreeSum.LightFixedRadixDictionary.program_meets_records {R : Type*} (records : List R) (raw : R → ℤ)
    {base dst p U J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hbase : base+records.length ≤ dst)
    (hm : 0 < records.length) (hbound : ∀ x ∈ records, |raw x| ≤ (U : ℤ))
    (hspace : LightRadixKeys.space dst records.length J ≤ lim.space)
    (hword : (LightRadixKeys.word p U J : ℤ) ≤ lim.word) (hd : d+J+3 ≤ lim.depth) :
    Meets lim (program (records.map raw)) 4 d [base,dst,J,p] μ (time (records.map raw) J)
      (fun r ν => r=((dst+LightRadixKeys.offset records.length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset records.length J)=((records.length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset records.length J+1)
          ((tuples records J).map (Radix.positionalHash (p : ℤ) raw)) ∧ Kept μ ν base) := by sorry
