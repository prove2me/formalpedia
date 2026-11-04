-- Prove2me | Theorems.Thm_ThreeSum_LightCoverSelect_program_meets
-- name    : ThreeSum.LightCoverSelect.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:58:21.71869+00:00
-- url     : https://prove2.me/theorems/1d9a3157-1c00-4261-919b-d5df8e6e0728
-- title:
--   Light Cover Select: program meets
-- statement:
--   The Light Cover Select construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverSelect.lean#L85-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverSelect.lean#L85-L102

import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverSelect
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCoverScores_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverSelect
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCoverSelect.program_meets
    {μ : ℕ → ℤ} {src activePtr work rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ work) (hactive : activePtr+cols ≤ work)
    (hspace : work+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim program 0 d [src,activePtr,work,rows,cols] μ (time rows cols)
      (fun r μ' =>
        r = (LightMinimum.least (fun i => -(LightCoverScores.score matrix active cols i : ℤ)) rows : ℤ) ∧
        SameOutside μ μ' work rows) := by sorry
