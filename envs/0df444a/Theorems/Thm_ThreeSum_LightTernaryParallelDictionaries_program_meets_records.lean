-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets_records
-- name    : ThreeSum.LightTernaryParallelDictionaries.program_meets_records
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:01:52.883144+00:00
-- url     : https://prove2.me/theorems/dfa13e18-c0c4-444a-98f7-34ca09ea20de
-- title:
--   Light Ternary Parallel Dictionaries: program meets records
-- statement:
--   Three arrays share exactly the same literal record tuple order. Equal
--   keys or equal map labels retain separate physical tuple occurrences.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryParallelDictionaries.lean#L122-L155
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryParallelDictionaries.lean#L122-L155

import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets_records

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryParallelDictionaries
open Light RadixKeyLists
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
variable {lim : Limits}

theorem ThreeSum.LightTernaryParallelDictionaries.program_meets_records {R : Type*} (records : List R) (raw0 raw1 raw2 : R → ℤ)
    {base0 dst0 base1 dst1 base2 dst2 p0 p1 p2 U0 U1 U2 J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase0 : base0+records.length ≤ dst0)
    (hnext0 : LightRadixKeys.space dst0 records.length J ≤ base1)
    (hbase1 : base1+records.length ≤ dst1)
    (hnext1 : LightRadixKeys.space dst1 records.length J ≤ base2)
    (hbase2 : base2+records.length ≤ dst2)
    (hspace2 : LightRadixKeys.space dst2 records.length J ≤ lim.space)
    (hm : 0 < records.length)
    (hb0 : ∀ x ∈ records, |raw0 x| ≤ (U0 : ℤ))
    (hb1 : ∀ x ∈ records, |raw1 x| ≤ (U1 : ℤ))
    (hb2 : ∀ x ∈ records, |raw2 x| ≤ (U2 : ℤ))
    (hw0 : (LightRadixKeys.word p0 U0 J : ℤ) ≤ lim.word)
    (hw1 : (LightRadixKeys.word p1 U1 J : ℤ) ≤ lim.word)
    (hw2 : (LightRadixKeys.word p2 U2 J : ℤ) ≤ lim.word)
    (hd : d+J+4 ≤ lim.depth) :
    Meets lim (program (records.map raw0) (records.map raw1) (records.map raw2)) 15 d
      [base0,dst0,base1,dst1,base2,dst2,J,p0,p1,p2] μ
      (time (records.map raw0) (records.map raw1) (records.map raw2) J)
      (fun r ν => r=((dst2+LightRadixKeys.offset records.length J : ℕ) : ℤ) ∧
        recordOutput ν dst0 records raw0 p0 J ∧ recordOutput ν dst1 records raw1 p1 J ∧
        recordOutput ν dst2 records raw2 p2 J ∧ Kept μ ν base0) := by sorry
