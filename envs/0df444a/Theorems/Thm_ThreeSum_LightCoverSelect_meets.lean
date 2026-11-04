-- Prove2me | Theorems.Thm_ThreeSum_LightCoverSelect_meets
-- name    : ThreeSum.LightCoverSelect.meets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:54:31.260379+00:00
-- url     : https://prove2.me/theorems/d4700ddd-ba86-4184-9da3-ca7dfd1e255d
-- title:
--   Light Cover Select: meets
-- statement:
--   The Light Cover Select construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverSelect.lean#L19-L52
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverSelect.lean#L19-L52

import Definitions.Def_Submission_ThreeSum_LightCoverScores
import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverSelect
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverSelect
open Light
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCoverSelect.meets {pMain pScores pDot pMinimum : ℕ}
    (hmain : P[pMain]? = some (body pScores pMinimum))
    (hscores : P[pScores]? = some (LightCoverScores.body pDot))
    (hdot : P[pDot]? = some LightBooleanDot.body)
    (hminimum : P[pMinimum]? = some LightMinimum.body)
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
    Meets lim P pMain d [src,activePtr,work,rows,cols] μ (time rows cols)
      (fun r μ' =>
        r = (LightMinimum.least (fun i => -(LightCoverScores.score matrix active cols i : ℤ)) rows : ℤ) ∧
        SameOutside μ μ' work rows) := by sorry
