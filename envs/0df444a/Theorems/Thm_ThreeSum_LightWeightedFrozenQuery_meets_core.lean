-- Prove2me | Theorems.Thm_ThreeSum_LightWeightedFrozenQuery_meets_core
-- name    : ThreeSum.LightWeightedFrozenQuery.meets_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:27:19.983627+00:00
-- url     : https://prove2.me/theorems/d98f9d00-92fc-4df5-9eb3-497840ba1c9e
-- title:
--   Light Weighted Frozen Query: meets core
-- statement:
--   The leaf assumptions are specifications of the physical binary-search/load
--   procedure, instantiated from real arrays by `meets` in the physical layer.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenMain.lean#L21-L162
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/FrozenMain.lean#L21-L162

import Definitions.Def_Submission_Weighted_FrozenTime
import Definitions.Def_Submission_Weighted_FrozenMain
import Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_cost_update_drop

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.WeightedFrozenQueryCost (cacheCost cost_update_drop)
open ThreeSum.WeightedEnumeration (digitCost)
open ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightWeightedFrozenQuery.meets_core {N pMain pLookup pDigit pZero pErase : ℕ}
    (hmain : P[pMain]?=some (body pMain pLookup pDigit pZero pErase))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (T bankCodes bankCount bankValues nearCodes nearCount nearValues powers L U : ℕ)
    (H : TritWord N→ℤ) (Q : TritWord N) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hspace : powers+(2*N+1)≤lim.space)
    (hword : ((2^(2*N+1) : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcutWord : (T : ℤ)+1≤lim.word)
    (hvalueWord : 4*((4^N : ℕ) : ℤ)*(U : ℤ)+3≤lim.word)
    (hpowers : Powers μ powers (2*N))
    (hH : ∀ R, |H R|≤(U : ℤ))
    (hargs : ∀ K≤N, ∀ R : TritWord N,
      ∀ x∈inputs N K (cacheCost R) T (address R) bankCodes bankCount bankValues
        nearCodes nearCount nearValues powers L, |x|≤lim.word)
    (hbankLeaf : ∀ K≤N, ∀ R : TritWord N, Below R Q → cacheCost R≤T →
      ∀ d, d+L+1≤lim.depth →
      Meets lim P pLookup d [bankCodes,bankCount,address R,bankValues,powers,L,K] μ
        (LightTernaryQueryLookup.time L)
        (fun v μ' => v=stageValue K H R ∧ μ'=μ))
    (hnearLeaf : ∀ R : TritWord N, Below R Q → T<cacheCost R →
      ∀ d, d+L+1≤lim.depth →
      Meets lim P pLookup d [nearCodes,nearCount,address R,nearValues,powers,L,0] μ
        (LightTernaryQueryLookup.time L)
        (fun v μ' => v=H R ∧ μ'=μ)) :
    ∀ K≤N, ∀ R : TritWord N, Below R Q → ∀ d, d+K+2*N+L+3≤lim.depth →
      Meets lim P pMain d
        (inputs N K (cacheCost R) T (address R) bankCodes bankCount bankValues
          nearCodes nearCount nearValues powers L) μ (queryTime L T K R)
        (fun v μ' => v=stageValue K H R ∧ μ'=μ) := by sorry
