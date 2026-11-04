-- Prove2me | Theorems.Thm_ThreeSum_LightCoverScores_program_meets
-- name    : ThreeSum.LightCoverScores.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:24:03.79375+00:00
-- url     : https://prove2.me/theorems/3cde0911-a780-41cf-9c32-321d1156ac43
-- title:
--   Light Cover Scores: program meets
-- statement:
--   The Light Cover Scores construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverScores.lean#L105-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverScores.lean#L105-L119

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverScores
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCoverScores.program_meets
    {μ : ℕ → ℤ} {src activePtr dst rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrc : src+rows*cols ≤ dst) (hactive : activePtr+cols ≤ dst)
    (hspace : dst+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim program 0 d [src,activePtr,dst,cols,rows] μ (time rows cols)
      (fun _ μ' => (∀ i < rows, μ' (dst+i) = -(score matrix active cols i : ℤ)) ∧
        SameOutside μ μ' dst rows) := by sorry
