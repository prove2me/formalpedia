-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_program_from_zero
-- name    : ThreeSum.LightTernaryWantedCanonical.program_from_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:18.619191+00:00
-- url     : https://prove2.me/theorems/584fc37c-c26f-4941-874b-a6f4df86c8df
-- title:
--   Light Ternary Wanted Canonical: program from zero
-- statement:
--   Uniform start state: every actual representation is emitted directly,
--   without enumerating the full global output dictionary.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedCanonical.lean#L400-L428
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedCanonical.lean#L400-L428

import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
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

theorem ThreeSum.LightTernaryWantedCanonical.program_from_zero {P R S C V work J d : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (hp : 2 ≤ P) (hN : 1 ≤ raws.length) (hR : 1 ≤ R) (hS : 1 ≤ S) (hC : 1 ≤ C)
    (hcap : ∀ x, (localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ))
    (hwords : ∀ i < raws.length, words.getD i 0 < R)
    (hmaps : ∀ i < raws.length, maps.getD i 0 < S)
    (hRW : (R : ℤ) ≤ lim.word) (hSW : (S : ℤ) ≤ lim.word)
    (hNW : (raws.length : ℤ) ≤ lim.word) (F : Emod.Pre lim P (2*V) work)
    (x : ℤ) (original dst : ℕ) (μ : ℕ → ℤ)
    (hx : |x| ≤ (V : ℤ)) (hc : (((2*R)^J : ℕ) : ℤ) ≤ lim.word)
    (hm : (((2*S)^J : ℕ) : ℤ) ≤ lim.word)
    (ho : (original : ℤ) ≤ lim.word) (hJ : (J : ℤ) ≤ lim.word)
    (hs : dst+3*C^J ≤ work) (hd : d+J+3 ≤ lim.depth) :
    Meets lim (program P R S raws words maps) 0 d [J,x,0,1,0,1,original,dst,work] μ
      ((overhead P V+stepCost V+40)*(J+1)*C^J)
      (fun r ν => r=((dst+3*(wantedCodes (P : ℤ) raws words maps J x R S 0 1 0 1).length : ℕ) : ℤ) ∧
        r ≤ ((dst+3*C^J : ℕ) : ℤ) ∧
        Seg ν dst (rowCells original (wantedCodes (P : ℤ) raws words maps J x R S 0 1 0 1)) ∧
        Kept μ ν dst) := by sorry
