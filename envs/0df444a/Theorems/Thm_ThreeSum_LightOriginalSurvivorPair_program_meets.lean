-- Prove2me | Theorems.Thm_ThreeSum_LightOriginalSurvivorPair_program_meets
-- name    : ThreeSum.LightOriginalSurvivorPair.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:19:59.694383+00:00
-- url     : https://prove2.me/theorems/b2431c5d-e513-42a5-8596-a0c15110a11e
-- title:
--   Light Original Survivor Pair: program meets
-- statement:
--   The Light Original Survivor Pair construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorPair.lean#L46-L128
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightOriginalSurvivorPair.lean#L46-L128

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorStage
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorPair
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightOriginalSurvivorStage_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightReportingFilter_program_meets
import Theorems.Thm_ThreeSum_LightReportingGather_program_meets

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivorPair
open Light ThreeSum.LightSubsetAddress ThreeSum.LightOriginalBucketFilter
open ThreeSum.LightOriginalCollisionCleanup ThreeSum.LightOriginalSurvivors
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : Limits}

theorem ThreeSum.LightOriginalSurvivorPair.program_meets {aBase nA bBase nB cBase nC keyB keyC histB histC q powers W L U d
    outB valueB packedB lengthB outC valueC packedC lengthC : ℕ}
    (μ : ℕ → ℤ) (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : aBase+nA ≤ outB) (hB : bBase+nB ≤ outB) (hC : cBase+nC ≤ outB)
    (hkB : keyB+nB ≤ outB) (hkC : keyC+nC ≤ outB)
    (hhB : histB+q ≤ outB) (hhC : histC+q ≤ outB) (hp : powers+(W+1) ≤ outB)
    (hB1 : outB+2*nB ≤ valueB) (hB2 : valueB+nB ≤ packedB) (hB3 : packedB+nB ≤ lengthB)
    (hBC : lengthB+1 ≤ outC)
    (hC1 : outC+2*nC ≤ valueC) (hC2 : valueC+nC ≤ packedC) (hC3 : packedC+nC ≤ lengthC)
    (hEnd : lengthC+1 ≤ lim.space)
    (hword : ((nB+nC+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hkeysB : ∀ i < nB, keysB i < q) (hkeysC : ∀ i < nC, keysC i < q)
    (hreadKB : ∀ i < nB, μ (keyB+i) = (keysB i : ℤ))
    (hreadKC : ∀ i < nC, μ (keyC+i) = (keysC i : ℤ))
    (hcountsB : ∀ k < q, μ (histB+k) = (counts keysB nB k : ℤ))
    (hcountsC : ∀ k < q, μ (histC+k) = (counts keysC nC k : ℤ))
    (hboundA : ∀ i < nA, |A i| ≤ U) (hboundB : ∀ i < nB, |B i| ≤ U)
    (hboundC : ∀ i < nC, |C i| ≤ U)
    (hreadA : ∀ i < nA, μ (aBase+i) = A i) (hreadB : ∀ i < nB, μ (bBase+i) = B i)
    (hreadC : ∀ i < nC, μ (cBase+i) = C i)
    (hvalueWord : 2*(U : ℤ)+3 ≤ lim.word) (hpowers : Powers μ powers W)
    (hsortedB : ∀ i j, i < j → j < nB → B i < B j)
    (hsortedC : ∀ i j, i < j → j < nC → C i < C j)
    (hL : L ≤ W) (hnB : nB < 2^L) (hnC : nC < 2^L) (hd : d+L+5 ≤ lim.depth) :
    Meets lim program 8 d
      [aBase,nA,bBase,nB,cBase,nC,keyB,keyC,histB,histC,q,powers,L,
        outB,valueB,packedB,lengthB,outC,valueC,packedC,lengthC]
      μ (time keysB keysC nA nB nC L)
      (fun ret ν =>
        ret = (if LightDeletedTwoSum.flag (badIndex keysB nB) B A C nC nA
          (badIndices keysB nB).length 1 = 0 then
          (LightDeletedTwoSum.flag (badIndex keysC nC) C A B nB nA
            (badIndices keysC nC).length (-1) : ℤ) else 1) ∧
        Output ν keysB B nB outB valueB packedB lengthB ∧
        Output ν keysC C nC outC valueC packedC lengthC ∧ Kept μ ν outB ∧
          LightOriginalSurvivorStage.Above μ ν lengthC ∧
          (∀ x, LightOriginalSurvivorStage.Unwritten outB nB valueB packedB (indices keysB nB).length lengthB x →
            LightOriginalSurvivorStage.Unwritten outC nC valueC packedC (indices keysC nC).length lengthC x →
            ν x = μ x)) := by sorry
