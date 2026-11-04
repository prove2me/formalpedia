-- Prove2me | Theorems.Thm_ThreeSum_LightCoverGreedy_Procs_meets_w3sum_ac885d1
-- name    : ThreeSum.LightCoverGreedy.Procs.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:07:10.829037+00:00
-- url     : https://prove2.me/theorems/2513b282-b706-4013-9123-c08f667043a8
-- title:
--   Procs: meets
-- statement:
--   The Procs construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverGreedy.lean#L62-L180
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightCoverGreedy.lean#L62-L180

import Definitions.Def_Submission_ThreeSum_LightCoverSelect
import Definitions.Def_Submission_ThreeSum_LightCoverUpdate
import Definitions.Def_Submission_ThreeSum_BooleanGreedy
import Definitions.Def_Submission_ThreeSum_LightCoverGreedy
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_2b9c97c844160a97
import Theorems.Thm_ThreeSum_LightCoverSelect_Procs_meets
import Theorems.Thm_ThreeSum_LightCoverSelect_meets
import Definitions.Def_WeightedCache3SUM_Alias_7c6295bca57f98dc
import Definitions.Def_WeightedCache3SUM_Alias_e1d95931a2ead3e4

set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverGreedy
open Light BooleanGreedy
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {d : ℕ}

theorem ThreeSum.LightCoverGreedy.Procs.meets_w3sum_ac885d1 {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {src activePtr rows cols rounds : ℕ}
    (matrix : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ activePtr)
    (hspace : activePtr+total rows cols rounds ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src,activePtr,rows,cols,rounds] μ (time rows cols rounds)
      (fun r μ' => r = (out activePtr rows cols : ℤ) ∧
        Seg μ' (out activePtr rows cols) ((choices matrix rows cols rounds).map (fun x : ℕ => (x : ℤ))) ∧
        (∀ j < cols, μ' (activePtr+j) = (active matrix rows cols rounds j : ℤ)) ∧
        SameOutside μ μ' activePtr (total rows cols rounds)) := by sorry
