-- Prove2me | Theorems.Thm_ThreeSum_LightLocalCoverRow_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightLocalCoverRow.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:08:02.400558+00:00
-- url     : https://prove2.me/theorems/0679040d-d40f-49bd-83f0-d20d86d03376
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverRow.lean#L41-L106
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightLocalCoverRow.lean#L41-L106

import Definitions.Def_Submission_ThreeSum_LightPairFlags
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRow
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_9176929b72776235
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Definitions.Def_WeightedCache3SUM_Alias_66dd70707634c020
import Definitions.Def_WeightedCache3SUM_Alias_cdc5e7727f35fd80

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverRow
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightLocalCoverRow.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap keys : ℕ}
    (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hbits : bitPtr+n*L ≤ keys) (hleft : leftPtr+n ≤ keys) (hright : rightPtr+n ≤ keys)
    (hleftHist : leftHist+p ≤ keys) (hrightHist : rightHist+p ≤ keys)
    (hdst : dst+p*p ≤ keys) (hspace : keys+2*(n*n) ≤ lim.space)
    (hword : (LightPairFlags.word L n p cap : ℤ) ≤ lim.word)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hleftRead : ∀ i < n, μ (leftPtr+i) = (left i : ℤ))
    (hrightRead : ∀ i < n, μ (rightPtr+i) = (right i : ℤ))
    (hleftLt : ∀ i < n, left i < p) (hrightLt : ∀ i < n, right i < p)
    (hleftCount : ∀ r < p, μ (leftHist+r) = (leftCount r : ℤ))
    (hrightCount : ∀ r < p, μ (rightHist+r) = (rightCount r : ℤ))
    (hleftBound : ∀ r < p, leftCount r ≤ n) (hrightBound : ∀ r < p, rightCount r ≤ n) :
    Meets lim P pMain d [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap,keys] μ (time L n p)
      (fun _ μ' =>
        (∀ r < p*p, μ' (dst+r) =
          (LightSupportMark.bit (LightPairFlags.pairKey n p left right)
            (LightPairFlags.pairFlag L n cap bits left right leftCount rightCount) r (n*n) : ℤ)) ∧
        KeptBut μ μ' keys dst (p*p)) := by sorry
