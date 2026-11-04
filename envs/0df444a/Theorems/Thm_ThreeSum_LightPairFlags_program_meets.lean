-- Prove2me | Theorems.Thm_ThreeSum_LightPairFlags_program_meets
-- name    : ThreeSum.LightPairFlags.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:06.806037+00:00
-- url     : https://prove2.me/theorems/e6aaf71d-834d-495f-ac90-25c70bbe4633
-- title:
--   Light Pair Flags: program meets
-- statement:
--   The Light Pair Flags construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairFlags.lean#L246-L268
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPairFlags.lean#L246-L268

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSum_LightTrimTest
import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightSmallDivide_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightPairFlags
open Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightPairFlags.program_meets
    {μ : ℕ → ℤ} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap : ℕ}
    (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hbits : bitPtr+n*L ≤ dst) (hleft : leftPtr+n ≤ dst) (hright : rightPtr+n ≤ dst)
    (hleftHist : leftHist+p ≤ dst) (hrightHist : rightHist+p ≤ dst)
    (hspace : dst+2*(n*n) ≤ lim.space) (hword : (word L n p cap : ℤ) ≤ lim.word)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hleftRead : ∀ i < n, μ (leftPtr+i) = (left i : ℤ))
    (hrightRead : ∀ i < n, μ (rightPtr+i) = (right i : ℤ))
    (hleftLt : ∀ i < n, left i < p) (hrightLt : ∀ i < n, right i < p)
    (hleftCount : ∀ r < p, μ (leftHist+r) = (leftCount r : ℤ))
    (hrightCount : ∀ r < p, μ (rightHist+r) = (rightCount r : ℤ))
    (hleftBound : ∀ r < p, leftCount r ≤ n) (hrightBound : ∀ r < p, rightCount r ≤ n) :
    Meets lim program 0 d [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap] μ (time L n)
      (fun _ μ' =>
        (∀ i < n*n, μ' (dst+i) = (pairKey n p left right i : ℤ)) ∧
        (∀ i < n*n, μ' (dst+n*n+i) = (pairFlag L n cap bits left right leftCount rightCount i : ℤ)) ∧
        SameOutside μ μ' dst (2*(n*n))) := by sorry
