-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets
-- name    : ThreeSum.LightTernaryParallelDictionaries.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:56:37.942584+00:00
-- url     : https://prove2.me/theorems/56bfdc05-c8da-456b-8b14-3130b2dd7a5f
-- title:
--   Light Ternary Parallel Dictionaries: program meets
-- statement:
--   The Light Ternary Parallel Dictionaries construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryParallelDictionaries.lean#L30-L112
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryParallelDictionaries.lean#L30-L112

import Definitions.Def_Submission_ThreeSum_LightFixedRadixDictionary
import Definitions.Def_Submission_ThreeSum_ReportingHostRelocation
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryParallelDictionaries
open Light RadixKeyLists
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
variable {lim : Limits}

theorem ThreeSum.LightTernaryParallelDictionaries.program_meets (xs ys zs : List ℤ)
    {base0 dst0 base1 dst1 base2 dst2 p0 p1 p2 U0 U1 U2 J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase0 : base0+xs.length ≤ dst0)
    (hnext0 : LightRadixKeys.space dst0 xs.length J ≤ base1)
    (hbase1 : base1+ys.length ≤ dst1)
    (hnext1 : LightRadixKeys.space dst1 ys.length J ≤ base2)
    (hbase2 : base2+zs.length ≤ dst2)
    (hspace2 : LightRadixKeys.space dst2 zs.length J ≤ lim.space)
    (hm0 : 0 < xs.length) (hm1 : 0 < ys.length) (hm2 : 0 < zs.length)
    (hb0 : ∀ x ∈ xs, |x| ≤ (U0 : ℤ))
    (hb1 : ∀ x ∈ ys, |x| ≤ (U1 : ℤ))
    (hb2 : ∀ x ∈ zs, |x| ≤ (U2 : ℤ))
    (hw0 : (LightRadixKeys.word p0 U0 J : ℤ) ≤ lim.word)
    (hw1 : (LightRadixKeys.word p1 U1 J : ℤ) ≤ lim.word)
    (hw2 : (LightRadixKeys.word p2 U2 J : ℤ) ≤ lim.word)
    (hd : d+J+4 ≤ lim.depth) :
    Meets lim (program xs ys zs) 15 d [base0,dst0,base1,dst1,base2,dst2,J,p0,p1,p2] μ
      (time xs ys zs J)
      (fun r ν => r=((dst2+LightRadixKeys.offset zs.length J : ℕ) : ℤ) ∧
        output ν dst0 xs p0 J ∧ output ν dst1 ys p1 J ∧ output ν dst2 zs p2 J ∧
        Kept μ ν base0) := by sorry
