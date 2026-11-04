-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryWantedCanonical_selector_ends
-- name    : ThreeSum.LightTernaryWantedCanonical.selector_ends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:04:56.64753+00:00
-- url     : https://prove2.me/theorems/d3c3437d-1d95-4ff8-ad80-45fc182dbe34
-- title:
--   Light Ternary Wanted Canonical: selector ends
-- statement:
--   The selector visits only the chosen fixed residue bucket.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedCanonical.lean#L232-L260
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryWantedCanonical.lean#L232-L260

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

theorem ThreeSum.LightTernaryWantedCanonical.selector_ends {pSelf pDivide P R S T r0 : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (l : List ℤ) (μ : ℕ → ℤ) (Q : State → Prop)
    (hres : frame l 11=(r0 : ℤ)) (hword : (r0 : ℤ) ≤ lim.word) :
    ∀ (rs : List ℕ), r0 ∈ rs → (∀ r ∈ rs, (r : ℤ) ≤ lim.word) →
    (∀ r ∈ rs, r0=r → Ends lim Prog d
      (recordSteps pSelf pDivide P R S raws words maps (localBucket (P : ℤ) raws (r : ℤ)))
      ⟨frame l,μ⟩ T Q) →
    Ends lim Prog d (selector pSelf pDivide P R S raws words maps rs) ⟨frame l,μ⟩
      (T+5*rs.length) Q := by sorry
