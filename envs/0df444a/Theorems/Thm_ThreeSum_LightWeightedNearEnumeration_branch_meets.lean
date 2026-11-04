-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedNearEnumeration_branch_meets
-- name    : ThreeSum.LightWeightedNearEnumeration.branch_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:46.285373+00:00
-- url     : https://prove2.me/theorems/93f98e7f-bae7-4655-8bc2-9e929b01b995
-- title:
--   Light Weighted Near Enumeration: branch meets
-- statement:
--   The Light Weighted Near Enumeration construction uses the branch meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L106-L203
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/LightNearEnumeration.lean#L106-L203

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_Weighted_NearEnumeration
import Definitions.Def_Submission_Weighted_LightNearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.WeightedAddresses
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.WeightedNearEnumeration
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedNearEnumeration.branch_meets {pBranch pSelf W N D pref dst powers caps d : ℕ}
    (hprog : P[pBranch]? = some (branchBody pSelf)) (qs : List ℕ) (q r : Fin 3)
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*W+1) ≤ lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hcontrol : ((1025*W+1100 : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers (2*W)) (hN : N ≤ W) (hlen : qs.length = N)
    (hDmax : D ≤ 1025*W) (hdst : dst ≤ lim.space) (hcaps : caps ≤ lim.space)
    (hpref : pref+digitCode r.val*4^N+4^N ≤ 4^W)
    (hChild : Allowed q.val r.val D →
      Meets lim P pSelf (d+1)
        [N,D-(digitCost q.val-digitCost r.val),pref+digitCode r.val*4^N,dst,powers,caps] μ
        (time qs (D-(digitCost q.val-digitCost r.val)))
        (fun count μ' => count = ((words qs (D-(digitCost q.val-digitCost r.val))).length : ℤ) ∧
          Seg μ' dst (output qs (D-(digitCost q.val-digitCost r.val)) (pref+digitCode r.val*4^N)) ∧
          SameOutside μ μ' dst (words qs (D-(digitCost q.val-digitCost r.val))).length))
    (hd : d+1 ≤ lim.depth) :
    Meets lim P pBranch d [N,D,pref,dst,powers,caps,digitCost q.val,digitCost r.val] μ
      (branchTime qs D q.val r.val)
      (fun count μ' => count = (branchCount qs D q.val r.val : ℤ) ∧
        Seg μ' dst (branchOutput qs D pref q.val r.val) ∧
        SameOutside μ μ' dst (branchCount qs D q.val r.val)) := by sorry
