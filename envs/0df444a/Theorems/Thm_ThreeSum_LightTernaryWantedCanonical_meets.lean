-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_meets
-- name    : ThreeSum.LightTernaryWantedCanonical.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:09:42.003863+00:00
-- url     : https://prove2.me/theorems/99df649a-ed41-4fd6-832f-993843cfe625
-- title:
--   Light Ternary Wanted Canonical: meets
-- statement:
--   A real program enumerates only the target's carry-compatible radix tuples.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedCanonical.lean#L263-L379
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedCanonical.lean#L263-L379

import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Definitions.Def_WeightedCache3SUM_Alias_fe1d986d2522f297
import Definitions.Def_WeightedCache3SUM_Alias_9c326f345c0ba28d
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_eb65baeba73fd57c
import Definitions.Def_WeightedCache3SUM_Alias_3b3552e2795ab46d
import Definitions.Def_WeightedCache3SUM_Alias_3252ff1ef14149f2
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c
import Definitions.Def_WeightedCache3SUM_Alias_d061ef657958844a
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4
import Theorems.Thm_ThreeSum_LightModuloCounts_Procs_meets
import Definitions.Def_WeightedCache3SUM_Alias_03cdb09d18890d4e
import Definitions.Def_WeightedCache3SUM_Alias_aeb4de5e6b301b55
import Definitions.Def_WeightedCache3SUM_Alias_375bd97fc128be02
import Definitions.Def_WeightedCache3SUM_Alias_9a4576158068ee52
import Definitions.Def_WeightedCache3SUM_Alias_9b3006da0fcbdf4e
import Theorems.Thm_ThreeSum_LightScaleArray_meets
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryDivide_meets
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_codeLimit_base
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_codeLimit_child
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedRadix_child_target_bound
import Theorems.Thm_ThreeSum_TernaryWantedRadix_codeLimit_base
import Theorems.Thm_ThreeSum_TernaryWantedRadix_codeLimit_child
import Theorems.Thm_ThreeSum_TernaryWantedRadix_localBucket_eq_of_emod
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedOutputs_length_le
attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedLittleEndian.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWantedCanonical
open Light
open TernaryWantedRadix (localBucket mem_localBucket localBucket_eq_of_emod wantedOutputs wantedOutputs_length_le child_target_bound codeLimit codeLimit_base codeLimit_child)
open TernaryWantedLittleEndian (wantedCodes wantedCodes_length wantedCodes_succ encode)
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
variable {lim : Limits} {Prog : Program} {d : ℕ}

theorem ThreeSum.LightTernaryWantedCanonical.meets {pMain pDivide pDecode pEmod P R S C V work : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (hmain : Prog[pMain]? = some (body pMain pDivide pEmod P R S raws words maps))
    (hdivide : Prog[pDivide]? = some (LightTernaryDivide.body pDecode))
    (hdecode : Prog[pDecode]? = some LightOutputDecodeDivide.body)
    (hem : Prog[pEmod]? = some emodBody)
    (hp : 2 ≤ P) (hN : 1 ≤ raws.length) (hR : 1 ≤ R) (hS : 1 ≤ S) (hC : 1 ≤ C)
    (hcap : ∀ x, (localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ))
    (hwords : ∀ i < raws.length, words.getD i 0 < R)
    (hmaps : ∀ i < raws.length, maps.getD i 0 < S)
    (hRW : (R : ℤ) ≤ lim.word) (hSW : (S : ℤ) ≤ lim.word) (hNW : (raws.length : ℤ) ≤ lim.word) (F : Emod.Pre lim P (2*V) work) :
    ∀ (J d : ℕ) (x : ℤ) (code scale mapCode mapScale original dst : ℕ) (μ : ℕ → ℤ),
      |x| ≤ (V : ℤ) → (codeLimit R code scale J : ℤ) ≤ lim.word →
      (codeLimit S mapCode mapScale J : ℤ) ≤ lim.word →
      (original : ℤ) ≤ lim.word → (J : ℤ) ≤ lim.word →
      dst+3*C^J ≤ work → d+J+3 ≤ lim.depth →
      Meets lim Prog pMain d [J,x,code,scale,mapCode,mapScale,original,dst,work] μ (time P C V J)
        (fun r ν => r=((dst+3*(wantedCodes (P : ℤ) raws words maps J x R S code scale mapCode mapScale).length : ℕ) : ℤ) ∧
          Seg ν dst (rowCells original (wantedCodes (P : ℤ) raws words maps J x R S code scale mapCode mapScale)) ∧
          Kept μ ν dst) := by sorry
