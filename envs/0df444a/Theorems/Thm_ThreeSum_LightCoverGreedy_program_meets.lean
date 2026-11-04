-- Prove2me | Theorems.Thm_ThreeSum_LightCoverGreedy_program_meets
-- name    : ThreeSum.LightCoverGreedy.program_meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:12:07.136518+00:00
-- url     : https://prove2.me/theorems/b5ea0ab7-fef4-408f-8e75-84ec8f977fea
-- title:
--   Light Cover Greedy: program meets
-- statement:
--   The Light Cover Greedy construction uses the program meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverGreedy.lean#L189-L204
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverGreedy.lean#L189-L204

import Definitions.Def_Submission_ThreeSum_LightCoverSelect
import Definitions.Def_Submission_ThreeSum_LightCoverUpdate
import Definitions.Def_Submission_ThreeSum_BooleanGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Theorems.Thm_ThreeSum_LightBooleanDot_program_meets
import Theorems.Thm_ThreeSum_LightCoverScores_program_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_program_meets
import Theorems.Thm_ThreeSum_LightCoverUpdate_program_meets

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverGreedy
open Light BooleanGreedy
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCoverGreedy.program_meets
    {μ : ℕ → ℤ} {src activePtr rows cols rounds : ℕ}
    (matrix : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ activePtr)
    (hspace : activePtr+total rows cols rounds ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim program 0 d [src,activePtr,rows,cols,rounds] μ (time rows cols rounds)
      (fun r μ' => r = (out activePtr rows cols : ℤ) ∧
        Seg μ' (out activePtr rows cols) ((choices matrix rows cols rounds).map (fun x : ℕ => (x : ℤ))) ∧
        (∀ j < cols, μ' (activePtr+j) = (active matrix rows cols rounds j : ℤ)) ∧
        SameOutside μ μ' activePtr (total rows cols rounds)) := by sorry
