-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalOffset_program_meets
-- name    : ThreeSum.LightOriginalOffset.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T12:02:25.659688+00:00
-- url     : https://prove2.me/theorems/6be2f3a3-d677-440c-81c4-082b815684e6
-- title:
--   Light Original Offset: program meets
-- statement:
--   The Light Original Offset construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalOffset.lean#L196-L207
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalOffset.lean#L196-L207

import Definitions.Def_Submission_ThreeSum_LightBalancedOffset
import Definitions.Def_Submission_ThreeSum_LightModuloCounts
import Definitions.Def_Submission_ThreeSum_LightOriginalOffset
import Theorems.Thm_ThreeSum_LightBalancedOffset_program_meets
import Theorems.Thm_ThreeSum_LightCapacity_program_meets
import Theorems.Thm_ThreeSum_LightCyclic_program_meets
import Theorems.Thm_ThreeSum_LightKaratsuba_program_meets
import Theorems.Thm_ThreeSum_LightLookupSum_program_meets
import Theorems.Thm_ThreeSum_LightModuloCounts_program_meets
import Theorems.Thm_ThreeSum_LightResidueHistogram_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightOriginalOffset
open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightOriginalOffset.program_meets {a b nLeft nRight p N free U : ℕ} [NeZero p] {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nLeft ≤ free) (hb : b+nRight ≤ free)
    (hnLeft : nLeft ≤ N) (hnRight : nRight ≤ N)
    (hspace : space free p N U ≤ lim.space) (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 p+4 ≤ lim.depth)
    (hLeft : ∀ i < nLeft, |μ (a+i)| ≤ (U : ℤ))
    (hRight : ∀ i < nRight, |μ (b+i)| ≤ (U : ℤ)) :
    Meets lim program 0 d [a,b,nLeft,nRight,p,N,free] μ (time p nLeft nRight U)
      (fun r ν => r = (selected p (fun i => μ (a+i)) (fun i => μ (b+i)) nLeft nRight : ℤ) ∧
        Kept μ ν free) := by sorry
