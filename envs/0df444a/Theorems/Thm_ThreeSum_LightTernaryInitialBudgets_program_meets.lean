-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryInitialBudgets_program_meets
-- name    : ThreeSum.LightTernaryInitialBudgets.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:32:22.089281+00:00
-- url     : https://prove2.me/theorems/57ff5286-7c53-4a70-964e-eb931163f70b
-- title:
--   Light Ternary Initial Budgets: program meets
-- statement:
--   Initial denominators and all three thresholds are genuine program
--   outputs. The paired threshold uses the actual requester/carry row count.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryInitialBudgets.lean#L38-L113
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryInitialBudgets.lean#L38-L113

import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryInitialBudgets
import Theorems.Thm_ThreeSum_LightNatPower_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryInitialBudgets
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem ThreeSum.LightTernaryInitialBudgets.program_meets {lim : Limits} {K bDigit a b scaleBase n J nO seed constants d : ℕ}
    (μ : ℕ → ℤ) (hn : 1≤n) (hbDigit : 1≤bDigit)
    (hw : (lim.space : ℤ)≤lim.word) (hseed : seed+47≤constants)
    (hspace : constants+3≤lim.space)
    (hword : (word K bDigit a b scaleBase n J nO : ℤ)≤lim.word) (hd : d<lim.depth) :
    Meets lim (program K bDigit a b scaleBase) 1 d [n,J,nO,seed,constants] μ (time K)
      (fun r ν => r=(initial K bDigit n J nO : ℤ) ∧
        Seg ν (seed+41) [1,1,1,((n*n : ℕ) : ℤ),((n*n : ℕ) : ℤ),(initial K bDigit n J nO : ℤ)] ∧
        Seg ν constants [(a : ℤ),b,scaleBase] ∧
        ∀ x, (x<seed+41 ∨ seed+47≤x) → (x<constants ∨ constants+3≤x) → ν x=μ x) := by sorry
