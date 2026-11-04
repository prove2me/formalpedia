-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryFrozenQuery_meets_core
-- name    : ThreeSum.LightTernaryFrozenQuery.meets_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:32:39.927637+00:00
-- url     : https://prove2.me/theorems/f17d0c6d-6c44-42a7-8382-721293207c0e
-- title:
--   Light Ternary Frozen Query: meets core
-- statement:
--   The leaf assumptions are specifications of the physical binary-search/load
--   procedure, instantiated from real arrays by `meets` in the physical layer.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryMain.lean#L13-L152
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryFrozenQueryMain.lean#L13-L152

import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryTime
import Definitions.Def_Submission_ThreeSum_LightTernaryFrozenQueryMain
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryFrozenQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightTernaryFrozenQuery.meets_core {N pMain pLookup pDigit pZero pErase : ℕ}
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
      ∀ x∈inputs N K (rank R) T (address R) bankCodes bankCount bankValues
        nearCodes nearCount nearValues powers L, |x|≤lim.word)
    (hbankLeaf : ∀ K≤N, ∀ R : TritWord N, Below R Q → rank R≤T →
      ∀ d, d+L+1≤lim.depth →
      Meets lim P pLookup d [bankCodes,bankCount,address R,bankValues,powers,L,K] μ
        (LightTernaryQueryLookup.time L)
        (fun v μ' => v=stageValue K H R ∧ μ'=μ))
    (hnearLeaf : ∀ R : TritWord N, Below R Q → T<rank R →
      ∀ d, d+L+1≤lim.depth →
      Meets lim P pLookup d [nearCodes,nearCount,address R,nearValues,powers,L,0] μ
        (LightTernaryQueryLookup.time L)
        (fun v μ' => v=H R ∧ μ'=μ)) :
    ∀ K≤N, ∀ R : TritWord N, Below R Q → ∀ d, d+K+2*N+L+3≤lim.depth →
      Meets lim P pMain d
        (inputs N K (rank R) T (address R) bankCodes bankCount bankValues
          nearCodes nearCount nearValues powers L) μ (queryTime L T K R)
        (fun v μ' => v=stageValue K H R ∧ μ'=μ) := by sorry
