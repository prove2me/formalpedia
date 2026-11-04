-- Prove2me | Theorems.Thm_ThreeSum_TernaryCanonicalDictionaries_program_meets
-- name    : ThreeSum.TernaryCanonicalDictionaries.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:44.678945+00:00
-- url     : https://prove2.me/theorems/89df90a8-131b-4117-a6e2-d9c3c769351d
-- title:
--   Ternary Canonical Dictionaries: program meets
-- statement:
--   Concrete canonical-field source initialization: native digit hash,
--   canonical word address and map occurrence code are generated from the
--   same trimmed local-record tuples in three independently stored arrays.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalDictionaries.lean#L65-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCanonicalDictionaries.lean#L65-L95

import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Theorems.Thm_ThreeSum_LightFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightFixedRadixDictionary_program_meets
import Theorems.Thm_ThreeSum_LightRadixKeys_program_meets
import Theorems.Thm_ThreeSum_LightRadixRows_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_program_meets
import Theorems.Thm_ThreeSum_LightTernaryParallelDictionaries_program_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalDictionaries
open Finset Light RadixKeyLists TernaryFixedDictionaries TernaryJointType
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {lim : Limits}

theorem ThreeSum.TernaryCanonicalDictionaries.program_meets (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    {base0 dst0 base1 dst1 base2 dst2 J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase0 : base0+(records (α := α) right maps B).length ≤ dst0)
    (hnext0 : LightRadixKeys.space dst0 (records (α := α) right maps B).length J ≤ base1)
    (hbase1 : base1+(records (α := α) right maps B).length ≤ dst1)
    (hnext1 : LightRadixKeys.space dst1 (records (α := α) right maps B).length J ≤ base2)
    (hbase2 : base2+(records (α := α) right maps B).length ≤ dst2)
    (hspace2 : LightRadixKeys.space dst2 (records (α := α) right maps B).length J ≤ lim.space)
    (hm : 0 < (records (α := α) right maps B).length)
    (hw0 : (LightRadixKeys.word p p J : ℤ) ≤ lim.word)
    (hw1 : (LightRadixKeys.word (4^L) (4^L) J : ℤ) ≤ lim.word)
    (hw2 : (LightRadixKeys.word (Fintype.card I) (Fintype.card I) J : ℤ) ≤ lim.word)
    (hd : d+J+4 ≤ lim.depth) :
    let rs := records (α := α) right maps B
    Meets lim (LightTernaryParallelDictionaries.program
      (rs.map (native right maps)) (rs.map wordCode) (rs.map mapCode)) 15 d
      [base0,dst0,base1,dst1,base2,dst2,J,p,4^L,Fintype.card I] μ
      (LightTernaryParallelDictionaries.time
        (rs.map (native right maps)) (rs.map wordCode) (rs.map mapCode) J)
      (fun r ν => r=((dst2+LightRadixKeys.offset rs.length J : ℕ) : ℤ) ∧
        LightTernaryParallelDictionaries.recordOutput ν dst0 rs (native right maps) p J ∧
        LightTernaryParallelDictionaries.recordOutput ν dst1 rs wordCode (4^L) J ∧
        LightTernaryParallelDictionaries.recordOutput ν dst2 rs mapCode (Fintype.card I) J ∧
        Kept μ ν base0) := by sorry
