-- Prove2me | Theorems.Thm_ThreeSum_LightBlockSourceHashes_program_meets
-- name    : ThreeSum.LightBlockSourceHashes.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:57:01.275961+00:00
-- url     : https://prove2.me/theorems/e074ce1d-bff5-4e1f-a1cc-543983922ed7
-- title:
--   Light Block Source Hashes: program meets
-- statement:
--   The fixed program returns the exact original block endpoints, rather
--   than an unspecified hash function supplied by its caller.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceHashes.lean#L151-L194
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBlockSourceHashes.lean#L151-L194

import Definitions.Def_Submission_ThreeSum_BlockCoefficientRows
import Definitions.Def_Submission_ThreeSum_LightMaskHashes
import Definitions.Def_Submission_ThreeSum_LightBlockSourceHashes
import Theorems.Thm_ThreeSum_LightBlockCoefficients_program_meets
import Theorems.Thm_ThreeSum_LightMaskHashes_program_meets
import Theorems.Thm_ThreeSum_LightOneHot_program_meets
import Theorems.Thm_ThreeSum_LightScaleArray_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockSourceHashes
open Light BlockCoefficientRows
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightBlockSourceHashes.program_meets
    {μ : ℕ → ℤ} {h J occ maps coeff0 coeff1 masks rawLeft rawRight n work : ℕ}
    (o : BlockEncoding.Occurrences h J)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h)))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d+J*(512*h)+2 ≤ lim.depth)
    (hspace : space work J (512*h) ≤ lim.space)
    (hocc : occ+J ≤ coeff0)
    (hmaps : maps+2*(512*h)*GlobalEncoding.scheduleSize h ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*(512*h) ≤ coeff1)
    (hc1 : coeff1+J*(512*h) ≤ rawLeft) (hleft : rawLeft+n ≤ rawRight)
    (hright : rawRight+n ≤ work)
    (hword : (word J (512*h) (LocalCoverBounds.localPrime h)
      (LocalCoverBounds.localPrime h) : ℤ) ≤ lim.word)
    (hselRead : ∀ j < J, μ (occ+j) = (occurrenceIndices o j : ℤ))
    (hread0 : ∀ s < GlobalEncoding.scheduleSize h, ∀ i < 512*h,
      μ (maps+2*(512*h)*s+i) = (mapRow h false s i : ℤ))
    (hread1 : ∀ s < GlobalEncoding.scheduleSize h, ∀ i < 512*h,
      μ (maps+2*(512*h)*s+512*h+i) = (mapRow h true s i : ℤ))
    (hmaskRead : ∀ i < n,
      μ (masks+i) = (SubsetAddress.subsetMask (BlockIndex.indexSet (sets i)) : ℤ)) :
    Meets lim program 0 d
      [J,512*h,LocalCoverBounds.localPrime h,occ,maps,coeff0,coeff1,masks,
        rawLeft,rawRight,n,work] μ (time J (512*h) n) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) = BlockEncoding.endpointLeft o (sets i)) ∧
        (∀ i < n, ν (rawRight+i) = BlockEncoding.endpointRight o (sets i)) ∧
        LightBlockCoefficients.Rows ν coeff0 coeff1 (512*h) (LocalCoverBounds.localPrime h)
          (occurrenceIndices o) (mapRow h false) (mapRow h true) J ∧
        Kept μ ν coeff0) := by sorry
