-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryNearEnumeration_branch_meets
-- name    : ThreeSum.LightTernaryNearEnumeration.branch_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:33:24.903812+00:00
-- url     : https://prove2.me/theorems/67c3e6b4-ede5-43b4-acb8-0713dc760bec
-- title:
--   Light Ternary Near Enumeration: branch meets
-- statement:
--   The Light Ternary Near Enumeration construction uses the branch meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumeration.lean#L118-L208
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryNearEnumeration.lean#L118-L208

import Definitions.Def_Submission_ThreeSum_LightTernaryEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryNearEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryNearEnumeration
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryNearEnumeration
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses
open ThreeSum.TernaryNearEnumeration
set_option maxHeartbeats 3000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryNearEnumeration.branch_meets {pBranch pSelf W N D pref dst powers caps d : ℕ}
    (hprog : P[pBranch]? = some (branchBody pSelf)) (qs : List ℕ) (q r : Fin 3)
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(2*W+1) ≤ lim.space)
    (hword : ((4^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers (2*W)) (hN : N ≤ W) (hlen : qs.length = N)
    (hDmax : D ≤ 2*W) (hdst : dst ≤ lim.space) (hcaps : caps ≤ lim.space)
    (hpref : pref+digitCode r.val*4^N+4^N ≤ 4^W)
    (hChild : Allowed q.val r.val D →
      Meets lim P pSelf (d+1)
        [N,D-(q.val-r.val),pref+digitCode r.val*4^N,dst,powers,caps] μ
        (time qs (D-(q.val-r.val)))
        (fun count μ' => count = ((words qs (D-(q.val-r.val))).length : ℤ) ∧
          Seg μ' dst (output qs (D-(q.val-r.val)) (pref+digitCode r.val*4^N)) ∧
          SameOutside μ μ' dst (words qs (D-(q.val-r.val))).length))
    (hd : d+1 ≤ lim.depth) :
    Meets lim P pBranch d [N,D,pref,dst,powers,caps,q.val,r.val] μ
      (branchTime qs D q.val r.val)
      (fun count μ' => count = (branchCount qs D q.val r.val : ℤ) ∧
        Seg μ' dst (branchOutput qs D pref q.val r.val) ∧
        SameOutside μ μ' dst (branchCount qs D q.val r.val)) := by sorry
