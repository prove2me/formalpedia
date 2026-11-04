-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryInitialKeys_program_meets
-- name    : ThreeSum.LightTernaryInitialKeys.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:21:57.403526+00:00
-- url     : https://prove2.me/theorems/bd1ff7ec-9058-4ae8-a8e9-8af153b7b232
-- title:
--   Light Ternary Initial Keys: program meets
-- statement:
--   The empty-prefix original keys are constructed by real zero fills.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryInitialKeys.lean#L17-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryInitialKeys.lean#L17-L47

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialKeys
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryInitialKeys
open Light
set_option maxHeartbeats 2000000

theorem ThreeSum.LightTernaryInitialKeys.program_meets {lim : Limits} {B nB C nC O nO d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hBC : B+nB≤C) (hCO : C+nC≤O)
    (hO : O+nO≤lim.space) (hd : d<lim.depth) :
    Meets lim program 1 d [B,nB,C,nC,O,nO] μ (time nB nC nO)
      (fun r ν => r=0 ∧ Kept μ ν B ∧
        (∀ i<nB, ν (B+i)=0) ∧ (∀ i<nC, ν (C+i)=0) ∧ (∀ i<nO, ν (O+i)=0)) := by sorry
