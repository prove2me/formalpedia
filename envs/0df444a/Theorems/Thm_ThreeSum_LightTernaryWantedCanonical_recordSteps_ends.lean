-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_recordSteps_ends
-- name    : ThreeSum.LightTernaryWantedCanonical.recordSteps_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:05:20.59799+00:00
-- url     : https://prove2.me/theorems/87df7f44-e3bd-433e-96e8-0263b2d2f076
-- title:
--   Light Ternary Wanted Canonical: record Steps ends
-- statement:
--   The Light Ternary Wanted Canonical construction uses the record Steps ends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedCanonical.lean#L105-L229
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedCanonical.lean#L105-L229

import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_LightSignedFiniteTable
import Definitions.Def_Submission_ThreeSum_LightTernaryDivide
import Definitions.Def_Submission_ThreeSum_LightResidues
import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightTernaryWantedCanonical
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_mem
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

theorem ThreeSum.LightTernaryWantedCanonical.recordSteps_ends {pMain pDivide pDecode P R S C V j : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (hdivide : Prog[pDivide]? = some (LightTernaryDivide.body pDecode))
    (hdecode : Prog[pDecode]? = some LightOutputDecodeDivide.body)
    (hp : 2 ≤ P) (hN : 1 ≤ raws.length) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hcap : ∀ x, (localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ))
    (hwords : ∀ i < raws.length, words.getD i 0 < R)
    (hmaps : ∀ i < raws.length, maps.getD i 0 < S)
    (x : ℤ) (code scale mapCode mapScale original baseDst work : ℕ)
    (F : Emod.Pre lim P (2*V) work) (hx : |x| ≤ (V : ℤ))
    (hc : (codeLimit R code scale (j+1) : ℤ) ≤ lim.word)
    (hm : (codeLimit S mapCode mapScale (j+1) : ℤ) ≤ lim.word)
    (ho : (original : ℤ) ≤ lim.word) (hJ : ((j+1 : ℕ) : ℤ) ≤ lim.word)
    (hRW : (R : ℤ) ≤ lim.word) (hSW : (S : ℤ) ≤ lim.word) (hNW : (raws.length : ℤ) ≤ lim.word) (hd : d+j+3 ≤ lim.depth)
    (hchild : ∀ (i : ℕ), i ∈ localBucket (P : ℤ) raws x →
      ∀ (dst : ℕ) (ν : ℕ → ℤ), dst+3*C^j ≤ work →
      Meets lim Prog pMain (d+1)
        [j,(x-raws.getD i 0)/(P : ℤ),code+scale*words.getD i 0,scale*R,mapCode+mapScale*maps.getD i 0,mapScale*S,original,dst,work]
        ν (time P C V j)
        (fun r ξ => r=((dst+3*(wantedCodes (P : ℤ) raws words maps j
          ((x-raws.getD i 0)/(P : ℤ)) R S (code+scale*words.getD i 0) (scale*R) (mapCode+mapScale*maps.getD i 0) (mapScale*S)).length : ℕ) : ℤ) ∧
          Seg ξ dst (rowCells original (wantedCodes (P : ℤ) raws words maps j
            ((x-raws.getD i 0)/(P : ℤ)) R S (code+scale*words.getD i 0) (scale*R) (mapCode+mapScale*maps.getD i 0) (mapScale*S))) ∧
          Kept ν ξ dst)) :
    ∀ (is : List ℕ), (∀ i ∈ is, i ∈ localBucket (P : ℤ) raws x) →
    ∀ (cursor : ℕ) (q residue : ℤ) (μ : ℕ → ℤ), cursor+3*is.length*C^j ≤ work →
      Ends lim Prog d (recordSteps pMain pDivide P R S raws words maps is)
        ⟨frame [j+1,x,code,scale,mapCode,mapScale,original,baseDst,work,q,cursor,residue],μ⟩
        (is.length*(stepCost V+time P C V j))
        (fun σ => ∃ q', σ.loc=frame [j+1,x,code,scale,mapCode,mapScale,original,baseDst,work,q',
          cursor+3*(branchCodes P R S raws words maps j x code scale mapCode mapScale is).length,residue] ∧
          Seg σ.mem cursor (rowCells original (branchCodes P R S raws words maps j x code scale mapCode mapScale is)) ∧
          Kept μ σ.mem cursor) := by sorry
