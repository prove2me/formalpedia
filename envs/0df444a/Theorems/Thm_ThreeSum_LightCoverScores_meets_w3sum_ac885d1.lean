-- Prove2me | Theorems.Thm_ThreeSum_LightCoverScores_meets_w3sum_ac885d1
-- name    : ThreeSum.LightCoverScores.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:24:02.286807+00:00
-- url     : https://prove2.me/theorems/80965233-81c5-4f7d-a80d-ae4833c209b9
-- title:
--   Light Cover Scores: meets
-- statement:
--   The Light Cover Scores construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverScores.lean#L34-L101
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverScores.lean#L34-L101

import Definitions.Def_Submission_ThreeSum_LightBooleanDot
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverScores
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCoverScores.meets_w3sum_ac885d1 {pMain pDot : ℕ}
    (hmain : P[pMain]? = some (body pDot))
    (hdot : P[pDot]? = some LightBooleanDot.body)
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
    Meets lim P pMain d [src,activePtr,dst,cols,rows] μ (time rows cols)
      (fun _ μ' => (∀ i < rows, μ' (dst+i) = -(score matrix active cols i : ℤ)) ∧
        SameOutside μ μ' dst rows) := by sorry
