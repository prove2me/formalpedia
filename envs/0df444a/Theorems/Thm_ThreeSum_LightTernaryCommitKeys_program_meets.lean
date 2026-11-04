-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCommitKeys_program_meets
-- name    : ThreeSum.LightTernaryCommitKeys.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:22:22.818771+00:00
-- url     : https://prove2.me/theorems/3aafff36-ba84-42e4-b962-0100c6180cc1
-- title:
--   Light Ternary Commit Keys: program meets
-- statement:
--   Copy the selected candidate's actual packed keys into the three retained
--   old-prefix buffers. All three source arrays are above the retained buffers,
--   so committing one side cannot change another side's source.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCommitKeys.lean#L19-L61
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCommitKeys.lean#L19-L61

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryCommitKeys
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCommitKeys
open Light
set_option maxHeartbeats 2000000

theorem ThreeSum.LightTernaryCommitKeys.program_meets {lim : Limits} {Bnew Bold nB Cnew Cold nC Onew Oold nO d : ℕ}
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ)≤lim.word)
    (hBC : Bold+nB≤Cold) (hCO : Cold+nC≤Oold)
    (hOB : Oold+nO≤Bnew) (hOC : Oold+nO≤Cnew) (hOO : Oold+nO≤Onew)
    (hB : Bnew+nB≤lim.space) (hC : Cnew+nC≤lim.space) (hO : Onew+nO≤lim.space)
    (hd : d<lim.depth) :
    Meets lim program 1 d [Bnew,Bold,nB,Cnew,Cold,nC,Onew,Oold,nO] μ (time nB nC nO)
      (fun r ν => r=0 ∧ Kept μ ν Bold ∧
        (∀ i<nB, ν (Bold+i)=μ (Bnew+i)) ∧
        (∀ i<nC, ν (Cold+i)=μ (Cnew+i)) ∧
        (∀ i<nO, ν (Oold+i)=μ (Onew+i)) ∧
        (∀ x, Oold+nO≤x → ν x=μ x)) := by sorry
