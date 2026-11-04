-- Prove2me | Theorems.Thm_ThreeSum_LightBandCandidatesCell_meets_w3sum_ac885d1
-- name    : ThreeSum.LightBandCandidatesCell.meets_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:50:44.980879+00:00
-- url     : https://prove2.me/theorems/2949177e-3fa3-491e-b7de-6332899e6f79
-- title:
--   Light Band Candidates Cell: meets
-- statement:
--   The Light Band Candidates Cell construction uses the meets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidatesCell.lean#L30-L77
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightBandCandidatesCell.lean#L30-L77

import Definitions.Def_Submission_ThreeSum_BandCandidateRows
import Definitions.Def_Submission_ThreeSum_LightBandCandidatesCell
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_d7235e9f603abd3f
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Definitions.Def_WeightedCache3SUM_Alias_737c7144994f79de
import Definitions.Def_WeightedCache3SUM_Alias_de0ba8c01a8a208c

set_option autoImplicit false
open ThreeSum ThreeSum.LightBandCandidatesCell
open Light BandCandidateRows
set_option maxHeartbeats 1400000
set_option maxRecDepth 6000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {r i j dst U : ℕ}

theorem ThreeSum.LightBandCandidatesCell.meets_w3sum_ac885d1 {pMain : ℕ} (mode : Mode)
    (hmain : P[pMain]?=some (body mode))
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst+4 ≤ lim.space)
    (hword : ((U+10 : ℕ) : ℤ) ≤ lim.word)
    (hr : r ≤ U) (hi : i ≤ U) (hj : j ≤ U) :
    Meets lim P pMain d [r,i,j,dst] μ time
      (fun _ ν => Seg ν dst (make mode i j r).cells ∧ SameOutside μ ν dst 4) := by sorry
